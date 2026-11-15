(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_S (catalog title "nat.axiom_leb_body_S"): for every
  natural number, the source polymorphic equality relates the Boolean
  less-than-or-equal test body at its successor to the natural-number matcher
  with false at zero and the preceding less-than-or-equal test at successors.
  This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem logipedia_nat_axiom_leb_body_S :
  forall n : nat,
    connectives_equal
      (nat -> bool)
      (leb_body (S n))
      (fun m : nat =>
         match_nat_type bool false (fun q : nat => leb n q) m).
Admitted.
