(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.eq_match_bool_type_false (catalog title
  "bool.eq_match_bool_type_false"): the polymorphic Boolean matcher at false
  is Leibniz-equal to its false branch. This file contains no proof.
*)

open HolKernel Parse boolLib;
open boolTheory;

val _ = new_constant (
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val bool_eq_match_bool_type_false =
  ``!(case_true : 'a) (case_false : 'a).
      logipedia_bool_match_bool_type case_true case_false F =
      case_false``;
