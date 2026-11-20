open HolKernel Parse boolLib bossLib;
val _ = new_theory "hello";

(* Two implication rules propagate p n through q n to r n. *)
val follows_from_local_rules = store_thm ("follows_from_local_rules",
  ``(!x : num. p x ==> q x) ==> (!x : num. q x ==> r x) ==> p n ==> q n /\ r n``,
  REPEAT DISCH_TAC THEN (CONJ_TAC THENL [METIS_TAC [], METIS_TAC []]));

val _ = export_theory ();
