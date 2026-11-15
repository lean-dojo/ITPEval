(*
  Statement-only formalization of the Logipedia corpus artifact
  bool.andb_true_l: if the conjunction of two Booleans is true, then its
  left operand is true. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logipedia_bool_andb_def = new_definition (
  "logipedia_bool_andb_def",
  ``logipedia_bool_andb (b1 : bool) (b2 : bool) =
      if b1 then b2 else F``);

val bool_andb_true_l =
  ``!(b1 : bool) (b2 : bool).
      logipedia_bool_andb b1 b2 = T
      ==>
      b1 = T``;
