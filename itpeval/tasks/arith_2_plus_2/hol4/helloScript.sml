open HolKernel Parse boolLib bossLib arithmeticTheory;

val _ = new_theory "hello";

val two_plus_two = save_thm ("two_plus_two", prove (``2 + 2 = 4``, EVAL_TAC));

val _ = export_theory();
