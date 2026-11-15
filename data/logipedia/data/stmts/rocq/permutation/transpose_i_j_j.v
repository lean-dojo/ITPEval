(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_j (catalog title "permutation.transpose_i_j_j"):
  transposing two natural numbers maps the second one to the first. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Theorem transpose_i_j_j :
  forall i j : nat,
    logipedia_permutation_transpose i j j = i.
Admitted.
