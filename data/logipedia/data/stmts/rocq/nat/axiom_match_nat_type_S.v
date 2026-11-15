(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_match_nat_type_S (catalog title
  "nat.axiom_match_nat_type_S"): for every result type, zero branch,
  successor branch, and natural number, the source polymorphic equality
  relates matching that number's successor to the successor branch applied
  to the number. This file contains no proof.
*)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter match_nat_type :
  forall return_type : Type,
    return_type -> (nat -> return_type) -> nat -> return_type.

Theorem logipedia_nat_axiom_match_nat_type_S :
  forall (return_type : Type)
         (case_O : return_type)
         (case_S : nat -> return_type)
         (n : nat),
    connectives_equal
      return_type
      (match_nat_type return_type case_O case_S (S n))
      (case_S n).
Admitted.
