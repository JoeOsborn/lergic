-module(lergic_tests).
-include_lib("eunit/include/eunit.hrl").
-compile({parse_transform,lergic}).

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
	)).

rel_cool_number(V) ->
	[VV || N <- [2,3,4],
	       VV <- lergic:bind(V,N)].

odd(V) -> (V rem 2) == 1.
double(V) -> V*2.

compound_terms_and_disj_rel_test() ->
	ExpectedOrderA = [{{term,a},{term,b},[{term,a},{term,b}]}],
	ExpectedOrderB = [{{term,b},{term,a},[{term,a},{term,b}]}],
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		link_between(_,_,_))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between(_,{term,b},_))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},_,_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},{term,a},_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},{term,a},[{term,a},{term,b}]))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b},_))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b},[{term,a},{term,b}]))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b},[_,_]))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b},[{term,a},_]))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,b},[_,{term,b}]))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},_,_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between(_,{term,a},_))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		link_between(_,{term,_},_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,_},{term,a},_))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,a},{term,_},_))),
	?assertEqual(ExpectedOrderB, lergic:all(
		link_between({term,b},{term,_},_))),
	?assertEqual(ExpectedOrderA, lergic:all(
		link_between({term,_},{term,b},_))),
	?assertEqual(ExpectedOrderA++ExpectedOrderB, lergic:all(
		link_between(_,_,[{term,a},{term,b}]))),
	?assertEqual([], lergic:all(
		link_between(_,_,[{term,b},{term,a}]))),
	ok.

%bidirectional link relation.
%maps from L1,L2 <-> [L1,L2] and L2,L1 <-> [L1,L2],
%if [L1,L2] is a link in AllLinks.
rel_link_between(L1,L2,LinkPair) ->
	AllLinks = [[{term,a},{term,b}]],
	lists:usort(
		[{L1V,L2V,[LA,LB]} ||
			ThisLink <- AllLinks,
			[LA,LB] <- lergic:bind(LinkPair,ThisLink),
			L1V <- lergic:bind(L1,LA),
			L2V <- lergic:bind(L2,LB)]++
		[{L1V,L2V,[LA,LB]} ||
			ThisLink <- AllLinks,
			[LA,LB] <- lergic:bind(LinkPair,ThisLink),
			L2V <- lergic:bind(L2,LA),
			L1V <- lergic:bind(L1,LB)]).
