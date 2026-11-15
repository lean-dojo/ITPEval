(*
  Statement-only formalization of Logipedia corpus artifact
  bool.true_or_false (catalog title "bool.true_or_false"): every Boolean value
  is equal to true or false. This file contains no proof.
*)

From Stdlib Require Import Bool.Bool.

Theorem bool_true_or_false :
  forall b : bool,
    b = true \/ b = false.
Admitted.
