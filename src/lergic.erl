-module(lergic).
%public API
-export([bind/2]).
%faux api visible in the parse transform:
-export([all/1, maybe/1, one/1, fn/1]).
-define(LERGIC_QUERIES,[all,maybe,one]).
%transformed from LC:
-export([all/2, maybe/2, one/2]).
%parse transform
-export([parse_transform/2]).
-export([do_transform/4, do_freshen/4, do_replace_variables/4]).
-compile({parse_transform,parse_trans_codegen}).

% lergic:all(
% 	fight_char(FID,CID), %bind $1,$2 for FID,CID
% 	char_ct(CID,CT), %replace CID with $2, bind $3 for CT
% 	char_speed(CID,Spd), %replace CID with $2, bind $4 for Spd
% 	char(CID,C), %replace CID with $2, bind $5 for C
%   PA = BPA + 3 % plus(BPA,3,PA), -->
%			% replace BPA with $N, bind $N+1 for PA
%   PA = -PB % {PBV,PAV} <- '-'(PB,PA)
% 	C#char{ct=lergic:fn(min(100,CT+Spd))}
%			% term, just let it slip by (but replace CT and Spd with $3,$4!)
%     % note too lergic:fn() to let a non-relational call go through!
% ) % ---->
%[CV#char{ct=min(100,CTV+SpdV)} ||
% {FIDV,CIDV} <- rel_fight_char(FID,CID),
% {CIDV,CTV} <- rel_char_ct(CIDV,'_'),
% {CIDV,SpdV} <- rel_char_speed(CIDV,'_'),
% {CIDV,CV} <- rel_char(CIDV,'_')]
% where '_' is specially interpreted by these relations.

%public API

all(_LC,Results) -> Results.
maybe(_LC,[]) -> false;
maybe(_LC,Results) -> Results.
one(_LC,[Result]) -> Result;
one(LC,Results) -> throw({lergic, expected_one, LC, Results}).

bind('_',V) -> [V];
bind({any,AVs},V) ->
	case lists:member(V,AVs) of
		true -> [V];
		false -> []
	end;
bind(V,V) -> [V];
bind(A,V) when is_tuple(A), is_tuple(V), size(A) == size(V) ->
	case lists:any(fun({AE,VE}) ->
		bind(AE,VE) == []
	end, lists:zip(tuple_to_list(A),tuple_to_list(V))) of
		true -> [];
		false -> [V]
	end;
bind(A,V) when is_list(A), is_list(V), length(A) == length(V) ->
	case lists:any(fun({AE,VE}) ->
		bind(AE,VE) == []
	end, lists:zip(A,V)) of
		true -> [];
		false -> [V]
	end;
bind(_A,_V) -> [].

%faux API

all(R) -> untransformed(all,R).
one(R) -> untransformed(one,R).
maybe(R) -> untransformed(maybe,R).
fn(R) -> untransformed(fn,R).

untransformed(F,R) ->
	throw({lergic,untransformed,F,
		"Please use the lergic parse transform when compiling this module.",
		{argument,R}}).

%parse transform

parse_transform(Forms, Options) ->
	AnnotatedForms = [erl_syntax_lib:annotate_bindings(F,[]) || F <- Forms],
	{Forms1,_S1} = parse_trans:transform(
		fun do_transform/4,
		sets:new(),
		AnnotatedForms,
		Options
	),
	% io:format("INPUT ~p~n", [AnnotatedForms]),
	% io:format("OUTPUT ~p~n", [Forms1]),
	% parse_trans:pp_src(parse_trans:revert(Forms1), "out.txt"),
	parse_trans:revert(Forms1).

do_transform(application, T, _Ctx, S) ->
	{Mod,Fn} = mod_fn(T),
	case {Mod,Fn,lists:member(Fn,?LERGIC_QUERIES)} of
		{lergic,Fn,true} ->
			{T2,S2} = transform_lergic_call(T,S),
			{T2,true,S2};
		{lergic,fn,false} ->
			{fn_to_call(T),false,S};
		{Mod,Fn,false} ->
			{call_to_rel(T),true,S}
	end;
do_transform(_,T,_,S) ->
	{T,true,S}.

fn_to_call(Term) ->
	hd(erl_syntax:application_arguments(Term)).

call_to_rel(Term) ->
	{Mod,Fn} = mod_fn(Term),
	RN = list_to_atom("rel_"++atom_to_list(Fn)),
	dup(Term, erl_syntax:application(
		case Mod of
			undefined -> dup(Term,erl_syntax:atom(RN));
			Mod -> dup(Term,erl_syntax:module_qualifier(Mod,RN))
		end,
		erl_syntax:application_arguments(Term)
	)).


deep_copy_pos(T,Dest) ->
	{[Ret],_} = parse_trans:transform(
		fun(_Type,TN,_,_) ->
			{dup(T,TN),true,undefined}
		end,
		undefined,
		[Dest],
		[]),
	Ret.

transform_lergic_call(T,Used) ->
	Args0 = erl_syntax:application_arguments(T),
	{Body,Template,BoundN} = case query_parts(Args0,[],Used) of
		{NewArgs,Tmpl,Set} ->
			{lists:reverse(NewArgs),Tmpl,Set};
		{NewArgs=[Last|_Rest],Set} ->
			{lists:reverse(NewArgs),
			case erl_syntax:type(Last) of
				generator -> erl_syntax:generator_pattern(Last);
				_ -> erl_syntax:atom(true)
			end,
			Set};
		Result ->
			io:format("Got result ~p~nfor T ~p~n", [Result,T]),
			throw({bad_query_parts,Result})
	end,
	[Comp] = parse_trans:revert([erl_syntax:list_comp(Template,Body)]),
	Ret = deep_copy_pos(T,erl_syntax:application(
		erl_syntax:application_operator(T),
		[
			lists:flatten(erl_pp:expr(hd(parse_trans:revert([T])))),
			Comp
		]
	)),
	{Ret,BoundN}.

query_parts([], Acc, Set) -> {Acc,Set};
query_parts([Term|Rest], Acc, Set) ->
	case erl_syntax:type(Term) of
		application ->
			{Rest2,Acc2,Set2} = query_parts_from_call(Term,Rest,Acc,Set),
			query_parts(Rest2,Acc2,Set2);
		match ->
			{Rest2,Acc2,Set2} = query_parts_from_match(Term,Rest,Acc,Set),
			query_parts(Rest2,Acc2,Set2);
		Type when Type == infix_expr; Type == prefix_expr ->
			%replace matches against ops with primitive predicates and anything else with a bind
			case query_parts_from_operator(Term,Rest,Acc,Set) of
				{finished,Acc,Term,Set} -> {Acc,Term,Set};
				{Rest2,Acc2,Set2} -> query_parts(Rest2,Acc2,Set2)
			end;
		_ when Rest == [] ->
			%it's a value expression, we're done!
			{Acc,Term,Set};
		_Type ->
			%it's a value expression but we're not done!
			throw({values_not_permitted_before_end,_Type,Term})
	end.

query_parts_from_call(Term,Rest,Acc,Set) ->
	{Mod,Fn} = mod_fn(Term),
	case {Mod,Fn} of
		{lergic,fn} ->
			%intended for functions that can return false
			Call = fn_to_call(Term),
			{V,Set2} = unused_variable_name(Set),
			Test = dup(Term,V),
			Generator = dup(Term,erl_syntax:generator(
				Test,
				erl_syntax:list([Call])
			)),
			{Rest,[Test,Generator|Acc],Set2};
		{lergic,_} -> throw({lergic,nested_lergic_transform,Fn,Term});
		{Mod,Fn} ->
			Op = erl_syntax:application_operator(Term),
			Args0 = erl_syntax:application_arguments(Term),
			{NewArgs,Template,Rest2,Set2} =
				 freshen_variables(Args0,Rest,Set),
			BoundPattern = case Template of
				[Unit] -> Unit;
				Template -> erl_syntax:tuple(Template)
			end,
			Generator = dup(Term,
				erl_syntax:generator(
					BoundPattern,
					%we're going to keep digging, so don't tack on the rel_ yet.
					erl_syntax:application(Op, NewArgs)
				)
			),
			{Rest2,[Generator|Acc],Set2}
	end.

%turn matches into "X from Y", i.e. generators
query_parts_from_match(Term,Rest,Acc,Set) ->
	%any fns inside will get replaced later
	L = erl_syntax:match_expr_pattern(Term),
	R = erl_syntax:match_expr_body(Term),
	%replace matches against ops with primitive predicates and anything else with a bind
	RHS = dup(R,case erl_syntax:type(R) of
		prefix_expr ->
			Op = erl_syntax:prefix_expr_operator(R),
			UR = erl_syntax:prefix_expr_argument(R),
			erl_syntax:application(erl_syntax:atom(lergic), Op, [UR,L]);
		infix_expr ->
			Op = erl_syntax:infix_expr_operator(R),
			LR = erl_syntax:infix_expr_left(R),
			RR = erl_syntax:infix_expr_right(R),
			erl_syntax:application(erl_syntax:atom(lergic), erl_syntax:atom(Op), [LR,RR,L]);
		application ->
			erl_syntax:application(erl_syntax:atom(lergic), erl_syntax:atom(bind), [L,R])
	end),
	{NewRHS,Template,NewRest,NewSet} =
		freshen_variables(erl_syntax:application_arguments(RHS), Rest, Set),
	Generator = dup(Term,
		erl_syntax:generator(
			erl_syntax:tuple(Template),
			NewRHS
		)
	),
	{NewRest,[Generator|Acc],NewSet}.

query_parts_from_operator(Term,Rest,Acc,Set) ->
	case is_guard(Term) of
		true ->
			%it's a guard, leave it as-is
			{Rest,[Term|Acc],Set};
		false when Rest == []->
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
	{Terms,{LHS,Rest,Set}} = parse_trans:transform(fun do_freshen/4, {Terms0,Rest0,Set0}, Terms0, []),
	{Terms,LHS,Rest,Set}.

do_freshen(underscore,V,_Ctx,{LHS,Rest,Set}) ->
	EnvVars = sets:from_list(proplists:append_values(env, erl_syntax:get_ann(V))),
	AllVars = sets:union(Set,EnvVars),
	{NVN,Set2} = unused_variable_name(AllVars),
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
			% otherwise, make a fresh variable and:
	{NVN,Set2} = unused_variable_name(AllVars),
	%   in either case, deep-replace all future occurrences of the variable in Rest and LHS with the fresh variable
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
	{Terms,_S} = parse_trans:transform(fun do_replace_variables/4, {OldName,NewName}, Trees, []),
	Terms;
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
	Terms;
replace_first_underscore(Tree,NewName) ->
	hd(replace_first_underscore([Tree],NewName)).

mod_fn(T) ->
	Op = erl_syntax:application_operator(T),
	case erl_syntax:type(Op) of
		atom -> {undefined,erl_syntax:atom_value(Op)};
		module_qualifier ->
			M = erl_syntax:module_qualifier_argument(Op),
			F = erl_syntax:module_qualifier_body(Op),
			{erl_syntax:atom_value(M),erl_syntax:atom_value(F)};
		_ -> {undefined,Op}
	end.

var_name(I) ->
	list_to_atom("_V"++integer_to_list(I)).

unused_variable_name(Used) ->
	V = erl_syntax_lib:new_variable_name(fun var_name/1, Used),
	{V, sets:add_element(V,Used)}.

dup(T, T2) ->
	erl_syntax:copy_ann(T, erl_syntax:copy_pos(T, T2)).