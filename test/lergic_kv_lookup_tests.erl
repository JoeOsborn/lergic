-module(lergic_kv_lookup_tests).
-include_lib("eunit/include/eunit.hrl").
-compile({parse_transform,lergic_kv}).
-lergic({lookup,rel}).

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
	)).

rel(boring_number,[V],Val) ->
	[{[VV],ValV} || N <- [0],
	       VV <- lergic:bind(V,N),
			   ValV <- lergic:bind(Val,true)];
rel(cool_number,[V],Val) ->
	[{[VV],ValV} || N <- [2,3,4],
	       VV <- lergic:bind(V,N),
			   ValV <- lergic:bind(Val,true)];
%bidirectional link relation.
%maps from L1,L2 <-> [L1,L2] and L2,L1 <-> [L1,L2],
%if [L1,L2] is a link in AllLinks.
rel(link_between,[L1,L2],LinkPair) ->
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

odd(V) -> (V rem 2) == 1.
double(V) -> V*2.

compound_terms_and_disj_rel_test() ->
	ExpectedOrderA = [{[{term,a},{term,b}],[{term,a},{term,b}]}],
	ExpectedOrderB = [{[{term,b},{term,a}],[{term,a},{term,b}]}],
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		link_between(AnyA,AnyB))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between(AnyA,{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},AnyB))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},{term,a}))),
	?assertEqual(ExpectedOrderB, lergic:all(
		[{term,a},{term,b}] = link_between({term,b},{term,a}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[{term,a},{term,b}] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[_,_] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[{term,a},_] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		[_,{term,b}] = link_between({term,a},{term,b}))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between(_,{term,a}))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		link_between(_,{term,_}))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,_},{term,a}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,_}))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},{term,_}))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,_},{term,b}))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		[{term,a},{term,b}] = link_between(_,_))),
	?assertEqual([], lergic:all(
		[{term,b},{term,a}] = link_between(_,_))),
	ok.
