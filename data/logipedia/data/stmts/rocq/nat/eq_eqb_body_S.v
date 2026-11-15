(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_eqb_body_S (catalog title "nat.eq_eqb_body_S"): for every natural
  number, Leibniz equality relates the Boolean equality-test body at its
  successor to the natural-number matcher with false at zero and the
  preceding equality test at successors. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.
Parameter eqb eqb_body : nat -> nat -> bool.

Theorem logipedia_nat_eq_eqb_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (eqb_body (S n))
      (fun m : nat =>
         match_nat_type bool false (fun q : nat => eqb n q) m).
Admitted.
