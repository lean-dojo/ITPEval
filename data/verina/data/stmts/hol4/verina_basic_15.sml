(*
  Statement-only formalization of VERINA corpus artifact verina_basic_15,
  catalog title "containsConsecutiveNumbers": the executable Boolean program
  scans an integer array for an adjacent pair whose second entry is one more
  than its first, together with its correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val containsConsecutiveNumbers_precond_def = new_definition (
  "containsConsecutiveNumbers_precond_def",
  ``containsConsecutiveNumbers_precond (a : int list) <=> T``
);

val containsConsecutiveNumbers_scan_def = Define `
  (containsConsecutiveNumbers_scan ([] : int list) = F) /\
  (containsConsecutiveNumbers_scan [x] = F) /\
  (containsConsecutiveNumbers_scan (x::y::rest) =
     if x + 1 = y then
       T
     else
       containsConsecutiveNumbers_scan (y::rest))
`;

val containsConsecutiveNumbers_def = new_definition (
  "containsConsecutiveNumbers_def",
  ``containsConsecutiveNumbers (a : int list) =
      if LENGTH a <= 1 then
        F
      else
        containsConsecutiveNumbers_scan a``
);

val containsConsecutiveNumbers_postcond_def = new_definition (
  "containsConsecutiveNumbers_postcond_def",
  ``containsConsecutiveNumbers_postcond
      (a : int list) (result : bool) <=>
      ((?i : num.
          i < LENGTH a - 1 /\
          EL i a + 1 = EL (i + 1) a) <=>
       result)``
);

val containsConsecutiveNumbers_spec_satisfied =
  ``!a : int list.
      containsConsecutiveNumbers_precond a ==>
      containsConsecutiveNumbers_postcond
        a (containsConsecutiveNumbers a)``;
