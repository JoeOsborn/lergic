-module(lergic_kv_tests).
-include_lib("eunit/include/eunit.hrl").
-compile({parse_transform,lergic_kv}).

matching_test() ->
	?assertEqual([], lergic:all(
		A = 1,
		A = 2
	)),
	?assertEqual([1], lergic:all(
		A = 1,
		A = 1
	)),
	?assertEqual([2], lergic:all(
		A = 1,
		B = 2
	)),
	?assertEqual([{1,1}], lergic:all(
		A = 1,
		B = A,
		{A,B}
	)),
	C = 2,
	?assertEqual([{1,2}], lergic:all(
		A = 1,
		B = C,
		{A,B}
	)),
	?assertEqual([], lergic:all(
		A = 1,
		B = A,
		B = C
	)),
	lergic:one(A=1),
	lergic:one(A=2),
	A = 1,
	lergic:one(A=1),
	?assertEqual([],lergic:all(A=2)),
	ok
	.

fn_test() ->
	A = 2,
	?assert(odd(3)),
	?assertNot(odd(2)),
	?assertNot(odd(4)),
	?assertEqual(4,double(2)),
	?assertEqual(8,double(4)),
	?assertEqual({2,4}, lergic:one(
		cool_number(A),
		B = lergic:fn(double(A)),
		cool_number(B),
		{A,B}
	)),
	?assertEqual(6, lergic:one(
		cool_number(V),
		lergic:fn(odd(V)),
		lergic:fn(double(V))
	)),
	?assertEqual(0, lergic:one(
		boring_number(V),
		V = lergic:fn(double(V)),
		V
	)),
	?assertEqual([3,4], lergic:all(
		cool_number(V),
		lergic:none(
			V2 = lergic:fn(double(V)),
			cool_number(V2)
		)
	)),
	?assertEqual([{a,[2,3,4]}], lergic:all(
		Vs = lergic:all(
			cool_number(V2)
		),
		{a,Vs}
	)),
	?assertEqual([{a,[2,3,4]}], lergic:all(
		{a,lergic:all(
			cool_number(V2)
		)}
	)).

rel_boring_number([V],Val) ->
	[{[VV],ValV} || N <- [0],
	       VV <- lergic:bind(V,N),
			   ValV <- lergic:bind(Val,VV)].

rel_cool_number([V],Val) ->
	[{[VV],ValV} || N <- [2,3,4],
	       VV <- lergic:bind(V,N),
			   ValV <- lergic:bind(Val,VV)].

odd(V) -> (V rem 2) == 1.
double(V) -> V*2.

compound_terms_and_disj_rel_test() ->
	ExpectedValue = [[{term,a},{term,b}]],
	ExpectedOrderA = [{[{term,a},{term,b}],[{term,a},{term,b}]}],
	ExpectedOrderB = [{[{term,b},{term,a}],[{term,a},{term,b}]}],
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		Ret = link_between(AnyA,AnyB))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between(AnyA,AnyB))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		[_RetA,_RetB] = link_between(AnyA,AnyB))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between(AnyA,{term,b}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,a},AnyB))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,b},{term,a}))),
	?assertEqual(ExpectedOrderB, lergic:all(
		[{term,a},{term,b}] = link_between({term,b},{term,a}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[{term,a},{term,b}] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[_,_] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[{term,a},_] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[_,{term,b}] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,b},_))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between(_,{term,a}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between(_,{term,_}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,_},{term,a}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,a},{term,_}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,b},{term,_}))),
	?assertEqual(ExpectedValue, lergic:all(
		link_between({term,_},{term,b}))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		[{term,a},{term,b}] = link_between(_,_))),
	?assertEqual([], lergic:all(
		[{term,b},{term,a}] = link_between(_,_))),
	ok.

%bidirectional link relation.
%maps from L1,L2 <-> [L1,L2] and L2,L1 <-> [L1,L2],
%if [L1,L2] is a link in AllLinks.
rel_link_between([L1,L2],LinkPair) ->
	AllLinks = [[{term,a},{term,b}]],
	lists:usort(
		[{[L1V,L2V],[LA,LB]} ||
			ThisLink <- AllLinks,
			[LA,LB] <- lergic:bind(LinkPair,ThisLink),
			L1V <- lergic:bind(L1,LA),
			L2V <- lergic:bind(L2,LB)]++
		[{[L1V,L2V],[LA,LB]} ||
			ThisLink <- AllLinks,
			[LA,LB] <- lergic:bind(LinkPair,ThisLink),
			L2V <- lergic:bind(L2,LA),
			L1V <- lergic:bind(L1,LB)]).
