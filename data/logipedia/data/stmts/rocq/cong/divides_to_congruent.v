(*
  Statement-only formalization of Logipedia corpus artifact
  cong.divides_to_congruent (catalog title "cong.divides_to_congruent"):
  divisibility of the truncated natural-number difference by a positive
  modulus implies congruence modulo that modulus. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition cong_congruent (n m p : nat) : Prop :=
  cong_source_mod n p = cong_source_mod m p.

Definition cong_divides (p a : nat) : Prop :=
  exists q : nat, a = p * q.

Theorem cong_divides_to_congruent :
  forall n m p : nat,
    0 < p ->
    m <= n ->
    cong_divides p (n - m) ->
    cong_congruent n m p.
Admitted.
