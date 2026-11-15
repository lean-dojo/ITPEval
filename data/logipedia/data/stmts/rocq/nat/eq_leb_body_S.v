(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_leb_body_S (catalog title "nat.eq_leb_body_S"): for every natural
  number, Leibniz equality relates the Boolean less-than-or-equal test body at
  its successor to the natural-number matcher with false at zero and the
  preceding less-than-or-equal test at successors. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem logipedia_nat_eq_leb_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (leb_body (S n))
      (fun m : nat =>
         match_nat_type bool false (fun q : nat => leb n q) m).
Admitted.
