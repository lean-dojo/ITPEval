(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_mod
  (catalog title "cong.mod_mod"): taking the natural-number remainder modulo
  a positive modulus is idempotent. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Theorem cong_mod_mod :
  forall n p : nat,
    0 < p ->
    cong_source_mod n p =
    cong_source_mod (cong_source_mod n p) p.
Admitted.
