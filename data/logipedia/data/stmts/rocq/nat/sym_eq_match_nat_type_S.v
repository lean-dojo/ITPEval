(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_match_nat_type_S (catalog title
  "nat.sym_eq_match_nat_type_S"): for every result type, zero branch,
  successor branch, and natural number, the successor-branch value is
  Leibniz-equal to evaluating the polymorphic natural-number eliminator at
  that number's successor. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_sym_eq_match_nat_type_S :
  forall (return_type : Type)
         (case_O : return_type)
         (case_S : nat -> return_type)
         (n : nat),
    logipedia_leibniz
      return_type
      (case_S n)
      (match_nat_type return_type case_O case_S (S n)).
Admitted.
