#lergic#

An embedded DSL for logic programming in Erlang, intended to replace deep lookups and updates to state objects with lots of lists of data. Nicer syntax than QLC for doing joins, and you can easily use arbitrary functions and relations in your query. See `test/lergic_tests.erl`.

There's also a transform called `lergic_kv` which treats queries as logical functions rather than relations (basically, blessing certain slots as "keys" and others as "values", and "returning" the values. Of course, this return value can be matched against; see `test/lergic_kv_tests.erl`.

Negation-as-failure is implemented in the simplest possible way. A `lergic:none` query inside of another query will take the values of any variables that have been bound so far, but variables bound within that `none` will not leak out to the enclosing query.

Lergic can also be seen as a reincarnation of mnemosyne; I intend to steal rule syntax for relation definition in the near future.

Relations can be backed by any kind of store (they are simply user-defined functions) and they are composed via a parse transform that turns queries into list comprehensions. If you're worried about nested loops, you can be careful to write for more queries and fewer searches, or you can update the parse transform to spit out QLC query handles rather than list comprehensions and send me a pull request.

The performance is likely to be very bad for relations defined in terms of other relations. It is currently implemented naively and simply and does no query optimization.

##Current bugs/pending features##
* Relations have to be defined by hand and handle `'_'` sigils on their own. It would be better to (have the option to) automatically produce them from `<-` syntax, probably as a different parse transform.
* No built-in relations have been defined for arithmetic operators &c. Those aren't hard, I just haven't needed them yet. They will need to handle ungrounded terms specially, of course, since I don't plan to implement a constraint solver.
* A query planner would be nice, but the work involved is probably non-trivial.
