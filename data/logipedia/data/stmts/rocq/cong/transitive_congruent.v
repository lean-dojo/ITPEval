(*
  Statement-only formalization of Logipedia corpus artifact
  cong.transitive_congruent (catalog title "cong.transitive_congruent"):
  for every natural modulus, congruence defined by equality of the source
  natural-number remainders is transitive. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition cong_source_mod (n p : nat) : nat :=
  match p with
  | O => n
  | S p' => Nat.modulo n (S p')
  end.

Definition cong_congruent (n m p : nat) : Prop :=
  cong_source_mod n p = cong_source_mod m p.

Definition cong_transitive {A : Type} (R : A -> A -> Prop) : Prop :=
  forall x y z : A,
    R x y -> R y z -> R x z.

Theorem cong_transitive_congruent :
  forall p : nat,
    cong_transitive (fun n m : nat => cong_congruent n m p).
Admitted.
