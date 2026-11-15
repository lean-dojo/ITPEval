(*
  Statement-only formalization of Logipedia corpus artifact bool.andb_true_r
  (catalog title "bool.andb_true_r"): if the conjunction of two Boolean
  values is true, then its right operand is true. This file contains no proof.
*)

From Stdlib Require Import Bool.Bool.

Theorem bool_andb_true_r :
  forall b1 b2 : bool,
    andb b1 b2 = true ->
    b2 = true.
Admitted.
