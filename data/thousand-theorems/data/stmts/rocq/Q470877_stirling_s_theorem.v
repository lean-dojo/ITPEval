(*
  Statement-only formalization of Thousand Theorems corpus artifact Q470877
  (thousand-theorems__rocq__Q470877), "Stirling's theorem": the Stirling
  sequence n! / (sqrt (2n) * (n / e)^n) converges to sqrt pi. This file
  contains no proof.
*)

From Stdlib Require Import Reals Arith.Factorial.

Open Scope R_scope.

Definition q470877_stirling_sequence (n : nat) : R :=
  INR (fact n) /
    (sqrt (2 * INR n) * (INR n / exp 1) ^ n).

Definition q470877_sequence_converges_to
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Theorem tendsto_stirling_sequence_sqrt_pi :
  q470877_sequence_converges_to
    q470877_stirling_sequence (sqrt PI).
Admitted.
