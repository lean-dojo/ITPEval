(*
  Statement-only formalization of Logipedia corpus artifact
  bool.eq_match_bool_type_false (catalog title
  "bool.eq_match_bool_type_false"): the polymorphic Boolean matcher applied
  to false is Leibniz-equal to its false branch for every result type and
  pair of branch values. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bool_type : Type.
Parameter bool_false : bool_type.
Parameter match_bool_type :
  forall return_type : Type,
    return_type -> return_type -> bool_type -> return_type.

Theorem bool_eq_match_bool_type_false :
  forall (return_type : Type)
         (case_true case_false : return_type),
    logipedia_leibniz
      return_type
      (match_bool_type return_type case_true case_false bool_false)
      case_false.
Admitted.
