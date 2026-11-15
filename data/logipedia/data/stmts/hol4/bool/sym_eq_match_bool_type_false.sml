(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.sym_eq_match_bool_type_false (catalog title
  "bool.sym_eq_match_bool_type_false"): the false branch is Leibniz-equal to
  the polymorphic Boolean matcher at false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open boolTheory;

val _ = new_constant (
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val bool_sym_eq_match_bool_type_false =
  ``!(case_true : 'a) (case_false : 'a).
      case_false =
      logipedia_bool_match_bool_type case_true case_false F``;
