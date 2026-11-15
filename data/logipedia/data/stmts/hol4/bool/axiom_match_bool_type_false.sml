(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.axiom_match_bool_type_false (catalog title
  "bool.axiom_match_bool_type_false"): the polymorphic Boolean matcher at
  false is related by the source equality predicate to its false branch.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val bool_axiom_match_bool_type_false =
  ``!(case_true : 'a) (case_false : 'a).
      logipedia_connectives_equal
        (logipedia_bool_match_bool_type case_true case_false F)
        case_false``;
