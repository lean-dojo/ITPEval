(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_i_j_j_i (catalog title
  "permutation.transpose_i_j_j_i"): a transposition of two natural numbers
  is unchanged when its two endpoints are exchanged. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Theorem transpose_i_j_j_i :
  forall i j n : nat,
    logipedia_permutation_transpose i j n =
    logipedia_permutation_transpose j i n.
Admitted.
