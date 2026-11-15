(*
  Statement-only formalization of VERINA artifact verina_advanced_22,
  cataloged as "isPeakValley": the executable Boolean program recognizes
  integer lists that strictly increase and then strictly decrease, with both
  phases nonempty. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory rich_listTheory;

val isPeakValley_precond_def = new_definition (
  "isPeakValley_precond_def",
  ``isPeakValley_precond (lst : int list) <=> T``
);

val isPeakValley_aux_def = Define `
  (isPeakValley_aux
      ([] : int list) (increasing : bool) (startedDecreasing : bool) =
     (increasing /\ startedDecreasing)) /\
  (isPeakValley_aux
      [x] increasing startedDecreasing =
     (increasing /\ startedDecreasing)) /\
  (isPeakValley_aux
      (x::y::rest) increasing startedDecreasing =
     if x < y then
       if startedDecreasing then
         F
       else
         isPeakValley_aux (y::rest) T startedDecreasing
     else if x > y then
       if increasing then
         isPeakValley_aux (y::rest) increasing T
       else
         F
     else
       F)
`;

val isPeakValley_def = new_definition (
  "isPeakValley_def",
  ``isPeakValley (lst : int list) =
      isPeakValley_aux lst F F``
);

val isPeakValley_validPeaks_def = new_definition (
  "isPeakValley_validPeaks_def",
  ``isPeakValley_validPeaks (lst : int list) =
      let len = LENGTH lst
      in
        FILTER
          (\p.
             1 <= p /\ p < len - 1 /\
             EVERY
               (\i. EL i lst < EL (i + 1) lst)
               (COUNT_LIST p) /\
             EVERY
               (\i. EL (p + i) lst > EL (p + i + 1) lst)
               (COUNT_LIST (len - 1 - p)))
          (COUNT_LIST len)``
);

val isPeakValley_postcond_def = new_definition (
  "isPeakValley_postcond_def",
  ``isPeakValley_postcond
      (lst : int list) (result : bool) <=>
      let validPeaks = isPeakValley_validPeaks lst
      in
        (validPeaks <> [] ==> result) /\
        (LENGTH validPeaks = 0 ==> ~result)``
);

val isPeakValley_spec_satisfied =
  ``!lst : int list.
      isPeakValley_precond lst ==>
      isPeakValley_postcond lst (isPeakValley lst)``;
