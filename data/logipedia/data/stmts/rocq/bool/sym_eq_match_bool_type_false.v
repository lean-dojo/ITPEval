(*
  Statement-only formalization of Logipedia corpus artifact
  bool.sym_eq_match_bool_type_false (catalog title
  "bool.sym_eq_match_bool_type_false"): the false branch is Leibniz-equal
  to the polymorphic Boolean matcher applied to false, for every result type
  and pair of branch values. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bool_type : Type.
Parameter bool_false : bool_type.
Parameter match_bool_type :
  forall return_type : Type,
    return_type -> return_type -> bool_type -> return_type.

Theorem bool_sym_eq_match_bool_type_false :
  forall (return_type : Type)
         (case_true case_false : return_type),
    logipedia_leibniz
      return_type
      case_false
      (match_bool_type return_type case_true case_false bool_false).
Admitted.
