(*
  Statement-only formalization of the Logipedia corpus artifact bigops.timesA:
  the opaque polymorphic Aop predicate holds for the successor of zero in the
  natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_bigops_Aop",
  Type.alpha --> Type.bool);

val bigops_timesA =
  ``logipedia_bigops_Aop (SUC 0 : num)``;
