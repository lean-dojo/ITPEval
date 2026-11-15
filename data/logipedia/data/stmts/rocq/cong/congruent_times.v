(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_times (catalog title "cong.congruent_times"):
  multiplication preserves congruence modulo a positive natural modulus.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition cong_congruent (n m p : nat) : Prop :=
  cong_source_mod n p = cong_source_mod m p.

Theorem cong_congruent_times :
  forall n m n1 m1 p : nat,
    0 < p ->
    cong_congruent n n1 p ->
    cong_congruent m m1 p ->
    cong_congruent (n * m) (n1 * m1) p.
Admitted.
