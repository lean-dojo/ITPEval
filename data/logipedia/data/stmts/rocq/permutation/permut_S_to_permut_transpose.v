(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_S_to_permut_transpose (catalog title
  "permutation.permut_S_to_permut_transpose"): a bounded permutation through
  a successor remains a bounded permutation on the preceding initial segment
  after transposing the successor with its image. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_permutation_injn
    (f : nat -> nat) (n : nat) : Prop :=
  forall i j : nat,
    i <= n ->
    j <= n ->
    f i = f j ->
    i = j.

Definition logipedia_permutation_permut
    (f : nat -> nat) (n : nat) : Prop :=
  (forall i : nat, i <= n -> f i <= n) /\
  logipedia_permutation_injn f n.

Definition logipedia_permutation_transpose
    (i j k : nat) : nat :=
  if Nat.eqb k i then j
  else if Nat.eqb k j then i
  else k.

Theorem permut_S_to_permut_transpose :
  forall (f : nat -> nat) (m : nat),
    logipedia_permutation_permut f (S m) ->
    logipedia_permutation_permut
      (fun n : nat =>
         logipedia_permutation_transpose
           (f (S m)) (S m) (f n))
      m.
Admitted.
