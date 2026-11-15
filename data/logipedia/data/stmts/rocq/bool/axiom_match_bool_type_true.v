(*
  Statement-only formalization of Logipedia corpus artifact
  bool.axiom_match_bool_type_true (catalog title
  "bool.axiom_match_bool_type_true"): the polymorphic true-branch
  computation law for the source Boolean eliminator, stated using
  connectives.equal. This file contains no proof.
*)

Parameter bool_type : Type.
Parameter bool_true : bool_type.
Parameter connectives_equal : forall A : Type, A -> A -> Prop.
Parameter match_bool_type :
  forall return_type : Type,
    return_type -> return_type -> bool_type -> return_type.

Theorem bool_axiom_match_bool_type_true :
  forall (return_type : Type)
         (case_true case_false : return_type),
    connectives_equal
      return_type
      (match_bool_type return_type case_true case_false bool_true)
      case_true.
Admitted.
