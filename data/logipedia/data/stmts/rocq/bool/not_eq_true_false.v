(*
  Statement-only formalization of Logipedia corpus artifact
  bool.not_eq_true_false (catalog title "bool.not_eq_true_false"): the Boolean
  values true and false are not equal. This file contains no proof.
*)

From Stdlib Require Import Bool.Bool.

Theorem bool_not_eq_true_false : true <> false.
Admitted.
