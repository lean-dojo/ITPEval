open HolKernel Parse boolLib;

val _ = new_theory "hello";

val hello_thm = prove(``T``, REWRITE_TAC[]);

(* ITPEVAL_AGENT_TARGET *)

val _ = export_theory();
