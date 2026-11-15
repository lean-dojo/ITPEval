(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.true_or_false (catalog title "bool.true_or_false"): every Boolean
  value is equal to true or equal to false. This file contains no proof.
*)

open HolKernel Parse boolLib;

val bool_true_or_false =
  ``!b : bool. b = T \/ b = F``;
