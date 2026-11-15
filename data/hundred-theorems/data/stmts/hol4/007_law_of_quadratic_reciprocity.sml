(*
  Statement-only formalization of "Law of Quadratic Reciprocity" from Hundred Theorems item 007.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory;

val law_of_quadratic_reciprocity =
  ``!(p : num) (q : num).
      prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q) ==>
      (if ?x : num. (x EXP 2) MOD q = p MOD q
       then (1 : int)
       else -1) *
      (if ?y : num. (y EXP 2) MOD p = q MOD p
       then (1 : int)
       else -1) =
      if EVEN (((p - 1) DIV 2) * ((q - 1) DIV 2))
      then (1 : int)
      else -1``;
