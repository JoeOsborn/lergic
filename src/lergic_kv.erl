-module(lergic_kv).
%the -lergic(lookup,Rel) attribute will turn calls
% of the form [V = ]module:relation(K...) into module:Rel(relation,K...,V).
-define(LERGIC_QUERIES,[all,maybe,one,none]).
-export([all_/2, maybe_/2, one_/2, none_/2]).
%parse transform
-export([parse_transform/2]).
-export([do_transform/4, do_freshen/4, do_replace_variables/4]).
-compile({parse_transform,parse_trans_codegen}).

% example:
% lergic:all(
% 	fight_char(FID,CID), %bind $1,$2 for FID,CID
% 	CT = char_ct(CID), %replace CID with $2, bind $3 for CT
% 	Spd = char_speed(CID), %replace CID with $2, bind $4 for Spd
% 	C = char(CID), %replace CID with $2, bind $5 for C
% 	C#char{ct=lergic:fn(min(100,CT+Spd))}
% 	  % term, just let it slip by (but replace CT and Spd with $3,$4)
% 	  % note too lergic:fn() to let a non-relational call go through
% ) % ---->
%[CV#char{ct=min(100,CTV+SpdV)} ||
% {[FIDV,CIDV],VV} <- rel_fight_char([FID,CID]),
% VV =/= false,
% {[CIDV],CTV} <- rel_char_ct([CIDV],'_'),
% {[CIDV],SpdV} <- rel_char_speed([CIDV],'_'),
% {[CIDV],CV} <- rel_char([CIDV],'_')]
% where '_' is specially interpreted by these relations.

-spec all_(string(),[A]) -> [A] when A :: term().
all_(_LC,Results) -> lists:usort(Results).
-spec maybe_(string(),[A]) -> false | [A] when A :: term().
maybe_(_LC,[]) -> false;
maybe_(_LC,Results) -> lists:usort(Results).
-spec one_(string(),[A]) -> A when A :: term().
one_(LC,Results) -> case lists:usort(Results) of
	[One] -> One;
	UResults -> throw({lergic, expected_one, LC, UResults})
end.
-spec none_(string(),[A]) -> false | [A] when A :: term().
none_(_LC,[]) -> true;
none_(_LC,_Results) -> false.


%parse transform

parse_transform(Forms, Options) ->
  Attributes = [A || {attribute, _, _, _}=A <- Forms],
	Others = [B || B <- Forms, element(1,B) =/= attribute],
	AnnotatedForms = [erl_syntax_lib:annotate_bindings(F,[]) || 
		F <- Attributes++Others],
	{Forms1,_S1} = parse_trans:transform(
		fun do_transform/4,
		{none,sets:new()},
		AnnotatedForms,
		Options
	),
	% io:format("INPUT ~p~n", [AnnotatedForms]),
	% io:format("OUTPUT ~p~n", [parse_trans:revert(Forms1)]),
	% parse_trans:pp_src(parse_trans:revert(Forms1), "out.txt"),
	parse_trans:revert(Forms1).

maybe_atom(undefined) -> undefined;
maybe_atom(A) when is_atom(A) -> A;
maybe_atom(T) ->
	case erl_syntax:type(T) of
		atom -> erl_syntax:atom_value(T);
		_ -> T
	end.
	
do_transform(attribute,T,_Ctx,S={_Lookup,Used}) ->
	case {
		maybe_atom(erl_syntax:attribute_name(T)),
		erl_syntax:attribute_arguments(T)
	} of
		{lergic,[Arg]} -> 
			[Prop,Val] = erl_syntax:tuple_elements(Arg),
			{lookup,Rel} = {maybe_atom(Prop),maybe_atom(Val)},
			{T,true,{{lookup,Rel},Used}};
		_ -> {T,true,S}
	end;
do_transform(function, T, Ctx, {Lookup,Used}) ->
	%on each pass through a function, change one query into an LC,
	%then re-analyze variable bindings. This is to avoid bindings from
	%one leaking out in the naive analysis and then poisoning later LCs.
	case parse_trans:transform(
		fun do_fun_transform/4,
		{false,Lookup,Used},
		[erl_syntax_lib:annotate_bindings(T,[])],
		[]
	) of
		{[NewT],{false,_,Used2}} -> 
			{NewT, false, {Lookup,Used2}};
		{[NewT],{true,_,Used2}} -> 
			do_transform(function, NewT, Ctx, {Lookup,Used2})
	end;
do_transform(_,T,_,S) ->
	{T,true,S}.

do_fun_transform(_, T, _Ctx, S={true,_Lookup,_Used}) -> {T,true,S};
do_fun_transform(application, T, Ctx, S={false,Lookup,Used}) ->
	% io:format("maybe transform ~p~n",[T]),
	{M,F} = mod_fn(T),
	% io:format("MFN:~p~n",[{M,F}]),
	try
	case {
		maybe_atom(M),
		lists:member(maybe_atom(F),?LERGIC_QUERIES)
	} of
		{lergic,true} ->
			% io:format("transforming call ~p~n",[T]),
			{T2,Used2} = transform_lergic_call(T,Lookup,Used),
			{[T3],_} = parse_trans:transform(fun do_munge_functions/4,
				Lookup,
				[T2],
				[]
			),
			% io:format("transformed call~n"),
			{T3,false,{true,Lookup,Used2}};
		_ ->
			{T,true,S}
	end
	catch _:Err -> io:format("top level error ~p~n",[{Ctx,Err}]), throw(Err) end;
do_fun_transform(_,T,_,S) ->
	{T,true,S}.

fn_to_call(Term) ->
	hd(erl_syntax:application_arguments(Term)).

call_to_rel(Term) ->
	{Mod,Fn} = mod_fn(Term),
	Name = atom_to_list(maybe_atom(Fn)),
	RN = case lists:prefix("rel_", Name) of
		true -> maybe_atom(Fn);
		false -> list_to_atom("rel_"++atom_to_list(maybe_atom(Fn)))
	end,
	dup(Term, erl_syntax:application(
		case Mod of
			undefined -> dup(Term,erl_syntax:atom(RN));
			Mod -> dup(Term,erl_syntax:module_qualifier(
				Mod,
				erl_syntax:atom(RN)
			))
		end,
		erl_syntax:application_arguments(Term)
	)).

deep_copy_pos(T,Dest) ->
	{[Ret],_} = parse_trans:transform(
		fun(_Type,TN,_,_) ->
			% io:format("Trying to copy into ~p~n",[TN]),
			{dup(T,TN),true,undefined}
		end,
		undefined,
		[Dest],
		[]
	),
	Ret.

transform_lergic_call(T,Lookup,Used) ->
	Args0 = erl_syntax:application_arguments(T),
	{Body,Template,Used2} = case query_parts(Args0,[],undefined,Lookup,Used) of
		{NewArgs,Tmpl,Set} when Tmpl =/= undefined ->
			{lists:reverse(NewArgs),Tmpl,Set};
		Result ->
			io:format("Got result ~p~nfor T ~p~n", [Result,T]),
			throw({bad_query_parts,Result})
	end,
	[Comp] = parse_trans:revert([erl_syntax:list_comp(Template,Body)]),
	CompStr =	lists:flatten(erl_pp:expr(hd(parse_trans:revert([T])))),
	Ret0 = erl_syntax:application(
		lergic:public_to_private(?MODULE,erl_syntax:application_operator(T)),
		[
			erl_syntax:string(CompStr),
			Comp
		]
	),
	Ret1 = deep_copy_pos(T,Ret0),
	{Ret1,Used2}.

do_munge_functions(application,T,_Ctx,Lookup) ->
	{M,F} = mod_fn(T),
	case {maybe_atom(M),maybe_atom(F)} of
		{lergic,fn} ->
			{fn_to_call(T),false,Lookup};
		{lergic,_Fn} ->
			{T,true,Lookup};
		{lergic_kv,_Fn} ->
			{T,true,Lookup};
		{_Mod,Fn} when is_atom(Fn), Lookup =/= none ->
			{T,true,Lookup};
		{_Mod,Fn} when is_atom(Fn) ->
			{call_to_rel(T),true,Lookup}
	end;
do_munge_functions(_Type,T,_Ctx,Lookup) ->
	{T,true,Lookup}.

query_parts([], Acc, Tmpl, _Lookup, Set) -> {Acc,Tmpl,Set};
query_parts([Term|Rest], Acc, Tmpl, Lookup, Set) ->
	case erl_syntax:type(Term) of
		application ->
			{Rest2,Acc2,Tmpl2,Set2} = 
				query_parts_from_call(Term,Rest,Acc,Lookup,Set),
			query_parts(Rest2,Acc2,lergic:next_template(Tmpl,Tmpl2),Lookup,Set2);
		match_expr ->
			{Rest2,Acc2,Tmpl2,Set2} = 
				query_parts_from_match(Term,Rest,Acc,Lookup,Set),
			query_parts(Rest2,Acc2,lergic:next_template(Tmpl,Tmpl2),Lookup,Set2);
		Type when Type == infix_expr; Type == prefix_expr ->
			%replace with primitive predicates and anything else with a bind
			case query_parts_from_operator(Term,Rest,Acc,Tmpl,Set) of
				{finished,Acc,Tmpl2,Set} -> {Acc,lergic:next_template(Tmpl,Tmpl2),Set};
				{Rest2,Acc2,Tmpl2,Set2} -> query_parts(Rest2,Acc2,lergic:next_template(Tmpl,Tmpl2),Lookup,Set2)
			end;
		_ when Rest == [] ->
			%it's a value expression, we're done!
			{Acc,Term,Set};
		_Type ->
			%it's a value expression but we're not done!
			throw({values_not_permitted_before_end,_Type,Term})
	end.

query_parts_from_call(Term,Rest,Acc,Lookup,Set) ->
	{M,F} = mod_fn(Term),
	case {maybe_atom(M),maybe_atom(F)} of
		{lergic,fn} ->
			%intended for functions that can return false
			Call = Term,
			{VN,Set2} = unused_variable_name(Set),
			Var = dup(Term,erl_syntax:variable(VN)),
			Test = dup(Term, erl_syntax:infix_expr(
				Var,
				dup(Term,erl_syntax:operator('=/=')),
				dup(Term,erl_syntax:atom(false))
			)),
			% io:format("Test:~p~n,Call:~p~n",[Test,Call]),
			Generator = dup(Term,erl_syntax:generator(
				Var,
				erl_syntax:list([Call])
			)),
			{Rest,[Test,Generator|Acc],Var,Set2};
		{lergic,none} -> 
			% [] == transform_lergic_call(lergic:all(...),Lookup,Set)
			{Call,Set2} = transform_lergic_call(
				dup(Term,erl_syntax:application(
					dup(Term,erl_syntax:atom(lergic)), 
					dup(Term,erl_syntax:atom(none_)),
					erl_syntax:application_arguments(Term)
				)),
				Lookup,
				Set
			),
			{Rest,[Call|Acc],'$prev',Set2};
		{lergic,Fn} -> throw({lergic,nested_lergic_transform,Fn,Term});
		{_Mod,_Fn} ->
			Op = erl_syntax:application_operator(Term),
			Args0 = erl_syntax:application_arguments(Term),
			{Rest2,Parts,BoundPattern,Set2} = relation_query(Op,Args0,undefined,Rest,Lookup,Set),
			%TODO: return just the Value part, not the Key part, as Boundpattern.
			[_K,V] = erl_syntax:tuple_elements(BoundPattern),
			{Rest2,lists:reverse(Parts)++Acc,V,Set2}
	end.

call_op_name(Op) ->
	case erl_syntax:type(Op) of
		atom -> erl_syntax:atom_value(Op);
		module_qualifier ->
			erl_syntax:atom_value(erl_syntax:module_qualifier_body(Op))
	end.

lookup_operator(Op,none) -> Op;
lookup_operator(Op,{lookup,Rel}) ->
	case erl_syntax:type(Op) of
		atom -> dup(Op,erl_syntax:atom(Rel));
		module_qualifier ->
			dup(Op,erl_syntax:module_qualifier(
				dup(Op,erl_syntax:module_qualifier_argument(Op)), 
				dup(Op,erl_syntax:atom(Rel))
			))
	end.

relation_query(Op, Key, Value, Rest, Lookup, Set) ->
	% io:format("turn ~p(~p,~p) into rel~n",[Op,Key,Value]),
	{NewKeyArgs,KeyTemplate,Rest2,Set2} = freshen_variables(Key,Rest,Set),
	{[NewValArg],[ValTemplate],Rest3,Set3} = case Value of
		undefined -> 
			{VN,Set2_1} = unused_variable_name(Set2),
			ValVar = erl_syntax:variable(VN),
			{[erl_syntax:atom('_')],[ValVar],Rest2,Set2_1};
		Value -> 
			%we dup op's properties into Value so that
			%the right variable-binding-status is given.
			% io:format("Op ~p~nVal ~p~n",[Op,Value]),
			freshen_variables([dup(Op,Value)],Rest2,Set2)
	end,
	KeyPattern = dup(Op,erl_syntax:list(KeyTemplate)),
	BoundPattern = dup(Op,erl_syntax:tuple([
		dup(Op,KeyPattern),
		dup(Op,ValTemplate)
	])),
	Call = dup(Op,erl_syntax:application(
		lookup_operator(Op,Lookup),
		case Lookup of 
			{lookup,_Rel} ->
				[dup(Op,erl_syntax:atom(call_op_name(Op)))];
			none -> 
				[]
		end++
		[dup(Op,erl_syntax:list(NewKeyArgs)),
		 dup(Op,NewValArg)]
	)),
	% io:format("Bound:~p~n,Call:~p~n",[BoundPattern,Call]),
	Generator = dup(Op,
		erl_syntax:generator(
			BoundPattern,
			%we're going to keep digging, so don't tack on the rel_ yet.
			Call
		)
	),
	{Rest3,[Generator]++case Value of 
		undefined -> 
			[dup(Op,erl_syntax:infix_expr(
				dup(Op,ValTemplate),
				dup(Op,erl_syntax:operator('=/=')),
				dup(Op,erl_syntax:atom(false))
			))];
		Value -> []
	end,BoundPattern,Set3}.

%turn matches into "X from Y", i.e. generators
query_parts_from_match(Term,Rest,Acc,Lookup,Set) ->
	%any fns inside will get replaced later
	L = erl_syntax:match_expr_pattern(Term),
	R = erl_syntax:match_expr_body(Term),
	%replace matches against rels with generators,
	%against prefix/infix ops with primitive predicates,
	%and anything else with a bind
	{M,F} = mod_fn(R),
	case {erl_syntax:type(R),maybe_atom(M),maybe_atom(F)} of
		{application,lergic,Fn} when Fn =/= fn ->
			throw({lergic,nested_lergic_transform,F,Term});
		{application,Mod,_Fn} when Mod =/= lergic ->
			{Rest2,Parts,BoundPattern,Set2} = relation_query(
				erl_syntax:application_operator(R),
				erl_syntax:application_arguments(R),
				L,
				Rest,
				Lookup,
				Set
			),
			{Rest2,lists:reverse(Parts)++Acc,BoundPattern,Set2};
		{prefix_expr,_,_} ->
			{Rest2,Parts,BoundPattern,Set2} = relation_query(
				dup(Term,erl_syntax:module_qualifier(
					erl_syntax:atom(lergic_kv),
					erl_syntax:prefix_expr_operator(R)
				)),
				[erl_syntax:prefix_expr_argument(R)],
				L,
				Rest,
				none,
				Set
			),
			{Rest2,lists:reverse(Parts)++Acc,BoundPattern,Set2};
		{infix_expr,_,_} ->
			{Rest2,Parts,BoundPattern,Set2} = relation_query(
				dup(Term,erl_syntax:module_qualifier(
					erl_syntax:atom(lergic_kv),
					erl_syntax:infix_expr_operator(R)
				)),
				[erl_syntax:infix_expr_left(R),erl_syntax:infix_expr_right(R)],
				L,
				Rest,
				none,
				Set
			),
			{Rest2,lists:reverse(Parts)++Acc,BoundPattern,Set2};
		_ ->
			{[L1],[BoundPattern],Rest2,Set2} = freshen_variables([L], Rest, Set),
			% io:format("match bind pattern ~p~ncall ~p~n",[BoundPattern,Call]),
			Generator = dup(Term,
				erl_syntax:generator(
					BoundPattern,
					dup(Term,erl_syntax:application(
						erl_syntax:atom(lergic),
						erl_syntax:atom(bind),
						[L1,R]
					))
				)
			),
			{Rest2,[Generator|Acc],BoundPattern,Set2}
	end.

query_parts_from_operator(Term,Rest,Acc,Tmpl,Set) ->
	case is_guard(Term) of
		true ->
			%it's a guard, leave it as-is and hope both sides are bound.
			%TODO: later, turn it into a relation with the same semantics
			%that could potentially generate examples.
			{Rest,[Term|Acc],Tmpl,Set};
		false when Rest == []->
			%TODO: should this be a relation instead, as in the match generator?
			%it's a value expression, we're done!
			{finished,Acc,Term,Set};
		false ->
			%it's a value expression but we're not done!
			throw({values_not_permitted_before_end,Term})
	end.

is_guard(Term) ->
	erl_lint:is_guard_test(hd(parse_trans:revert([Term]))).

freshen_variables(Terms0,Rest0,Set0) ->
	% io:format("Freshen ~p~n",[Terms0]),
	try
	{Terms,{LHS,Rest,Set}} = parse_trans:transform(fun do_freshen/4,
		{Terms0,Rest0,Set0},
		Terms0,
		[]
	),
	{Terms,LHS,Rest,Set}
	catch _:Err -> io:format("freshen error ~p~n",[Err]), throw(Err) end.

do_freshen(underscore,V,_Ctx,{LHS,Rest,Set}) ->
	{NVN,Set2} = unused_variable_name(Set),
	% io:format("replace underscore with ~p~n",[NVN]),
	LHS2 = replace_first_underscore(LHS,NVN),
	V2 = dup(V, erl_syntax:atom('_')),
	{V2,false,{LHS2,Rest,Set2}};
do_freshen(variable,V,_Ctx,{LHS,Rest,Set}) ->
	EnvVars = sets:from_list(proplists:append_values(env, erl_syntax:get_ann(V))),
	AllVars = sets:union(Set,EnvVars),
	VN = erl_syntax:variable_name(V),
	%EVEN IF the variable is bound in set, we still need a fresh variable on the LHS
	%        because generators require their LHS to have no free vars.
	{NVN,Set2} = unused_variable_name(Set),
	%   deep-replace all future occurrences of the variable in Rest and LHS with the fresh variable
	LHS2 = replace_variables(LHS,VN,NVN),
	% io:format("Old LHS:~p~nNew LHS:~p~n",[LHS,LHS2]),
	Rest2 = replace_variables(Rest,VN,NVN),
	V2 = case sets:is_element(VN, AllVars) of
		%if the variable is bound in the parent context, use it as is
		true ->
			V;
		%if the variable is not bound in the parent context, replace it with an '_' in the Term
		false ->
			dup(V, erl_syntax:atom('_'))
	end,
	{V2,false,{LHS2,Rest2,Set2}};
	%for each term in ArgsI, use the dict-deep-replacement of that term as the corresponding term in a tuple on the LHS.
do_freshen(_,T,_Ctx,{LHS,Rest,Set}) ->
	{T,true,{LHS,Rest,Set}}.

replace_variables(Trees,OldName,NewName) when is_list(Trees) ->
	try
	{Terms,_S} = parse_trans:transform(fun do_replace_variables/4, {OldName,NewName}, Trees, []),
	Terms
	catch _:Err -> io:format("replace variables error ~p~n",[Err]),throw(Err) end;
replace_variables(Tree,OldName,NewName) ->
	hd(replace_variables([Tree],OldName,NewName)).

do_replace_variables(variable,V,_Ctx,S={OldName,NewName}) ->
	V2 = case erl_syntax:variable_name(V) of
		OldName -> dup(V, erl_syntax:variable(NewName));
		_ -> V
	end,
	{V2,false,S};
do_replace_variables(_,T,_Ctx,S) ->
	{T,true,S}.


replace_first_underscore(Trees,NewName) when is_list(Trees) ->
	try
	{Terms,_FoundAny} = parse_trans:transform(
		fun(underscore,T,_Ctx,false) ->
			T2 = dup(T, erl_syntax:variable(NewName)),
			{T2,false,true};
		   (_,T,_,Done) ->
			{T,true,Done}
		end,
		false,
		Trees,
		[]
	),
	Terms
	catch _:Err -> io:format("replace underscore error ~p~n", [Err]) end;
replace_first_underscore(Tree,NewName) ->
	hd(replace_first_underscore([Tree],NewName)).

mod_fn(T) ->
	case erl_syntax:type(T) of
		application ->
			Op = erl_syntax:application_operator(T),
			case erl_syntax:type(Op) of
				module_qualifier ->
					M = erl_syntax:module_qualifier_argument(Op),
					F = erl_syntax:module_qualifier_body(Op),
					{M,F};
				_ ->
					{undefined,Op}
			end;
		_ -> {undefined,undefined}
	end.

var_name(I) ->
	list_to_atom("_LERG_"++integer_to_list(I)).

unused_variable_name(Used) ->
	V = erl_syntax_lib:new_variable_name(fun var_name/1, Used),
	{V, sets:add_element(V,Used)}.

dup(T, T2) ->
	erl_syntax:copy_ann(T, erl_syntax:copy_pos(T, T2)).