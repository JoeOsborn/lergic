#lergic#

An embedded DSL for logic programming in Erlang, intended to replace deep lookups and updates to state objects with lots of lists of data. Nicer syntax than QLC for doing joins, and you can easily use arbitrary functions and relations in your query. See `test/lergic_tests.erl`.

Lergic can also be seen as a reincarnation of mnemosyne; I intend to steal rule syntax for relation definition as my next step.

Relations can be backed by any kind of store--I like to pass along the `'_'` sigil into match-specs--and they work via a parse transform that turns queries into list comprehensions. If you're worried about nested loops, you can be careful to write for more queries and fewer searches, or you can update the parse transform to spit out QLC query handles rather than list comprehensions and send me a pull request.

##Current bugs/pending features##
* Relations have to be defined by hand and handle `'_'` sigils on their own.
* Matches in queries (not as common as relation-checks in queries) have to have bound variables on the right hand side.
* No built-in relations have been defined for arithmetic operators &c. Those aren't hard, I just haven't needed them yet. They will need to handle ungrounded terms specially, of course.
* Negation-as-failure.
* Modifying the knowledge-base.