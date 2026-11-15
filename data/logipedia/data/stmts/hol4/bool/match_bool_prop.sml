(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.match_bool_prop (catalog title "bool.match_bool_prop"): any predicate
  on Booleans that holds at true and false holds for every Boolean.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val bool_match_bool_prop =
  ``!(return_ : bool -> bool).
      return_ T ==>
      return_ F ==>
      !z : bool. return_ z``;
