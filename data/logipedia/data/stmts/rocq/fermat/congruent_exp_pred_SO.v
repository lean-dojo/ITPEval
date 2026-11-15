(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_exp_pred_SO (catalog title
  "fermat.congruent_exp_pred_SO"): Fermat's little theorem states that a
  natural number not divisible by a natural prime has predecessor-prime
  power congruent to one modulo that prime. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition fermat_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Definition fermat_prime (p : nat) : Prop :=
  1 < p /\
  forall m : nat,
    fermat_divides m p ->
    1 < m ->
    m = p.

Fixpoint fermat_exp (a n : nat) : nat :=
  match n with
  | O => 1
  | S k => fermat_exp a k * a
  end.

Definition fermat_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition fermat_congruent (n m p : nat) : Prop :=
  fermat_mod n p = fermat_mod m p.

Theorem congruent_exp_pred_SO :
  forall p a : nat,
    fermat_prime p ->
    ~ fermat_divides p a ->
    fermat_congruent (fermat_exp a (Nat.pred p)) 1 p.
Admitted.
