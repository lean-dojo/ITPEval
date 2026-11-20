open HolKernel Parse boolLib bossLib;
val _ = new_theory "hello";
val itpeval_target = store_thm ("itpeval_target", ``p ==> p /\ p``, PROVE_TAC []);
val _ = export_theory ();
