These are solutions of the exercises from the [prop-prove tutorial of Isabelle](https://isabelle.in.tum.de/doc/prog-prove.pdf) done both in Isabelle and Idris 2.
Also, some examples from the tutorial text also present.

I'm not claiming that all of solutions are optimal or somewhat nice.
Moreover, some of Idris solutions are not exactly correct because some tasks are not exactly applicable to Idris.

Also, some technical issues present.
For example, standard library of Idris seems to not contain properties of arithmetics operations upon integers,
thus exercises that involve them were solved with naturals, not integers.

Also, some of exercises were upon *sets* but (at least, at the time) there's no appropriate sets in the standard library.
Thus, my solutions contain some (non-minimal) implementation of intensional sets which support both propositional and standard ``Eq``-based equality.
