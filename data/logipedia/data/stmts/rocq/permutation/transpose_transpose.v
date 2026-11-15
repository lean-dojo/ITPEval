(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.transpose_transpose (catalog title
  "permutation.transpose_transpose"): applying the same transposition of two
  natural numbers twice returns every natural number unchanged. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Theorem transpose_transpose :
  forall i j n : nat,
    logipedia_permutation_transpose i j
      (logipedia_permutation_transpose i j n) = n.
Admitted.
