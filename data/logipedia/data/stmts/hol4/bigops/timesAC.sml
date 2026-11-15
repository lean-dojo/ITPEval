(*
  Statement-only formalization of Logipedia corpus artifact bigops.timesAC
  (catalog title "bigops.timesAC"): the source polymorphic ACop predicate holds
  at the natural number one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_bigops_ACop",
  Type.alpha --> Type.bool);

val bigops_timesAC =
  ``logipedia_bigops_ACop (SUC 0 : num)``;
