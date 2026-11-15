(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7208500
  (thousand-theorems__rocq__Q7208500), "Poisson limit theorem": if the real
  sequence n * p(n) converges to r, then the corresponding fixed-k binomial
  probability term converges to exp(-r) * r^k / k!. This file contains no
  proof.
*)

From Stdlib Require Import Reals Arith.PeanoNat.

Local Open Scope R_scope.

Fixpoint q7208500_choose (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' =>
      q7208500_choose n' k' + q7208500_choose n' (S k')
  end.

Fixpoint q7208500_factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * q7208500_factorial m
  end.

Definition q7208500_tendsto_real
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Theorem q7208500_canonical_statement :
  forall (p : nat -> R) (r : R) (k : nat),
    q7208500_tendsto_real
      (fun n : nat => INR n * p n) r ->
    q7208500_tendsto_real
      (fun n : nat =>
        INR (q7208500_choose n k) *
        (p n) ^ k *
        (1 - p n) ^ (n - k)%nat)
      (exp (-r) * (r ^ k) / INR (q7208500_factorial k)).
Admitted.
