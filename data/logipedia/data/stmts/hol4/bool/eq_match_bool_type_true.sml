(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.eq_match_bool_type_true (catalog title
  "bool.eq_match_bool_type_true"): the polymorphic Boolean matcher at true is
  Leibniz-equal to its true branch. This file contains no proof.
*)

open HolKernel Parse boolLib;
open boolTheory;

val _ = new_constant (
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val bool_eq_match_bool_type_true =
  ``!(case_true : 'a) (case_false : 'a).
      logipedia_bool_match_bool_type case_true case_false T =
      case_true``;
