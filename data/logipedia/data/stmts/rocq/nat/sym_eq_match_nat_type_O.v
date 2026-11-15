(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_match_nat_type_O (catalog title
  "nat.sym_eq_match_nat_type_O"): for every result type, zero branch, and
  successor branch, the zero-branch value is Leibniz-equal to evaluating the
  polymorphic natural-number eliminator at zero. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_sym_eq_match_nat_type_O :
  forall (return_type : Type)
         (case_O : return_type)
         (case_S : nat -> return_type),
    logipedia_leibniz
      return_type
      case_O
      (match_nat_type return_type case_O case_S O).
Admitted.
