(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_to_divides (catalog title "cong.congruent_to_divides"):
  congruence modulo a positive natural modulus implies that the modulus
  divides the truncated natural-number difference. This file contains no
  proof.
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

Theorem cong_congruent_to_divides :
  forall n m p : nat,
    0 < p ->
    cong_congruent n m p ->
    cong_divides p (n - m).
Admitted.
