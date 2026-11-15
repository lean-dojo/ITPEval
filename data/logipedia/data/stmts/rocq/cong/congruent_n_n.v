(*
  Statement-only formalization of Logipedia corpus artifact
  cong.congruent_n_n (catalog title "cong.congruent_n_n"): every natural
  number is congruent to itself modulo any natural modulus. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition cong_congruent (n m p : nat) : Prop :=
  cong_source_mod n p = cong_source_mod m p.

Theorem cong_congruent_n_n :
  forall n p : nat,
    cong_congruent n n p.
Admitted.
