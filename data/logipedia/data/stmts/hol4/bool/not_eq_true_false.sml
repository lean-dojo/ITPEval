(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.not_eq_true_false (catalog title "bool.not_eq_true_false"): Boolean
  truth is not equal to Boolean falsehood. This file contains no proof.
*)

open HolKernel Parse boolLib;

val bool_not_eq_true_false =
  ``~(T = F)``;
