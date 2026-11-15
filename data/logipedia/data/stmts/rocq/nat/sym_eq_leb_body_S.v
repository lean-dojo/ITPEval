(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_S (catalog title "nat.sym_eq_leb_body_S"): for every
  natural number, Leibniz equality relates the natural-number matcher with
  false at zero and the preceding Boolean less-than-or-equal test at successors
  to the less-than-or-equal-test body at the given successor. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.
Parameter leb leb_body : nat -> nat -> bool.

Theorem logipedia_nat_sym_eq_leb_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> bool)
      (fun m : nat =>
         match_nat_type bool false (fun q : nat => leb n q) m)
      (leb_body (S n)).
Admitted.
