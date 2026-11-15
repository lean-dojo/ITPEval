(*
  Statement-only formalization of Logipedia corpus artifact cong.mod_times
  (catalog title "cong.mod_times"): reducing a product modulo a positive
  natural modulus is unchanged when both factors are reduced first.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Theorem cong_mod_times :
  forall n m p : nat,
    0 < p ->
    cong_source_mod (n * m) p =
    cong_source_mod
      (cong_source_mod n p * cong_source_mod m p) p.
Admitted.
