(*
  Statement-only formalization of Logipedia corpus artifact
  bool.sym_eq_match_bool_type_true (catalog title
  "bool.sym_eq_match_bool_type_true"): the true branch is Leibniz-equal
  to the polymorphic Boolean matcher applied to true, for every result type
  and pair of branch values. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bool_type : Type.
Parameter bool_true : bool_type.
Parameter match_bool_type :
  forall return_type : Type,
    return_type -> return_type -> bool_type -> return_type.

Theorem bool_sym_eq_match_bool_type_true :
  forall (return_type : Type)
         (case_true case_false : return_type),
    logipedia_leibniz
      return_type
      case_true
      (match_bool_type return_type case_true case_false bool_true).
Admitted.
