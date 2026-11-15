(*
  Statement-only formalization of Logipedia corpus artifact
  cong.eq_times_plus_to_congruent (catalog title
  "cong.eq_times_plus_to_congruent"): an equality expressing one natural
  number as a multiple of a positive modulus plus another implies congruence
  modulo that modulus. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition cong_congruent (n m p : nat) : Prop :=
  cong_source_mod n p = cong_source_mod m p.

Theorem cong_eq_times_plus_to_congruent :
  forall n m p r : nat,
    0 < p ->
    n = r * p + m ->
    cong_congruent n m p.
Admitted.
