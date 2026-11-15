(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_O (catalog title
  "nat.axiom_match_nat_type_O"): for every result type, zero branch, and
  successor branch, the source polymorphic equality relates matching natural
  zero to the zero branch. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_axiom_match_nat_type_O :
  forall (return_type : Type)
         (case_O : return_type)
         (case_S : nat -> return_type),
    connectives_equal
      return_type
      (match_nat_type return_type case_O case_S O)
      case_O.
Admitted.
