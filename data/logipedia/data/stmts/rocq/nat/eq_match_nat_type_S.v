(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_match_nat_type_S (catalog title "nat.eq_match_nat_type_S"):
  evaluating the polymorphic natural-number eliminator at a successor is
  Leibniz-equal to the successor branch applied to its predecessor. This file
  contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_eq_match_nat_type_S :
  forall (return_type : Type)
         (case_O : return_type)
         (case_S : nat -> return_type)
         (n : nat),
    logipedia_leibniz
      return_type
      (match_nat_type return_type case_O case_S (S n))
      (case_S n).
Admitted.
