(*
  Statement-only formalization of the Logipedia corpus artifact logic.sym_eq
  (catalog title "logic.sym_eq"): equality is symmetric for every pair of
  elements of an arbitrary type. This file contains no proof.
*)

open HolKernel Parse boolLib;

val logic_sym_eq =
  ``!(x : 'a) (y : 'a).
      x = y ==> y = x``;
