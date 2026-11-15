(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1227703
  (thousand-theorems__rocq__Q1227703), "Dirichlet's approximation theorem":
  for every point of the additive circle of positive circumference T and
  every positive n, some multiple indexed from 1 through n has circle norm
  at most T/(n+1). Real representatives modulo the lattice T Z are used.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Reals ZArith.ZArith.

Local Open Scope R_scope.

Definition q1227703_circle_norm_le
    (T x bound : R) : Prop :=
  exists k : Z,
    Rabs (x - IZR k * T) <= bound.

Theorem AddCircle_exists_norm_nsmul_le :
  forall (T xi : R) (n : nat),
    0 < T ->
    (0 < n)%nat ->
    exists j : nat,
      (1 <= j)%nat /\
      (j <= n)%nat /\
      q1227703_circle_norm_le
        T (INR j * xi) (T / INR (S n)).
Admitted.
