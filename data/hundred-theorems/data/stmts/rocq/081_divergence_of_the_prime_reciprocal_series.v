(*
  Statement-only formalization of Hundred Theorems artifact 081,
  "Divergence of the Prime Reciprocal Series": the real partial sums of
  reciprocals of primes tend to positive infinity. This file contains no proof.
*)

From Stdlib Require Import Reals List PeanoNat.

Open Scope R_scope.

Definition primeb (p : nat) : bool :=
  andb (Nat.leb 2 p)
    (forallb
       (fun d => negb (Nat.eqb (Nat.modulo p d) 0))
       (seq 2 (p - 2))).

Definition prime_reciprocal (p : nat) : R :=
  if primeb p then / INR p else 0.

Fixpoint prime_reciprocal_sum (n : nat) : R :=
  match n with
  | O => 0
  | S k => prime_reciprocal_sum k + prime_reciprocal (S k)
  end.

Definition tends_to_pos_infinity (u : nat -> R) : Prop :=
  forall bound : R,
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        bound <= u n.

Theorem prime_reciprocal_series_diverges :
  tends_to_pos_infinity prime_reciprocal_sum.
Admitted.
