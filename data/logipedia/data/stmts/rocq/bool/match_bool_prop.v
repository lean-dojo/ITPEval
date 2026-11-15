(*
  Statement-only formalization of Logipedia corpus artifact
  bool.match_bool_prop (catalog title "bool.match_bool_prop"): the
  proposition-level Boolean elimination principle stating that a predicate
  holding at the distinguished true and false values holds for every Boolean.
  This file contains no proof.
*)

Parameter bool_type : Type.
Parameter bool_true bool_false : bool_type.

Theorem bool_match_bool_prop :
  forall return_ : bool_type -> Prop,
    return_ bool_true ->
    return_ bool_false ->
    forall z : bool_type, return_ z.
Admitted.
