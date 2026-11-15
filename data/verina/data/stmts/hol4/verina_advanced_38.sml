(*
  Statement-only formalization of VERINA artifact verina_advanced_38,
  cataloged as "maxCoverageAfterRemovingOne": the executable program removes
  each interval in turn, stably sorts the remainder by starting point, merges
  overlaps, and returns the greatest total coverage. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory;

val maxCoverageAfterRemovingOne_precond_def = new_definition (
  "maxCoverageAfterRemovingOne_precond_def",
  ``maxCoverageAfterRemovingOne_precond
      (intervals : (num # num) list) <=>
      LENGTH intervals > 0``
);

val maxCoverageAfterRemovingOne_eraseIdx_def = Define `
  (maxCoverageAfterRemovingOne_eraseIdx
      ([] : (num # num) list) (i : num) =
     ([] : (num # num) list)) /\
  (maxCoverageAfterRemovingOne_eraseIdx (x::xs) 0 = xs) /\
  (maxCoverageAfterRemovingOne_eraseIdx (x::xs) (SUC i) =
     x::maxCoverageAfterRemovingOne_eraseIdx xs i)
`;

val maxCoverageAfterRemovingOne_insertByStart_def = Define `
  (maxCoverageAfterRemovingOne_insertByStart
      (x : num # num) ([] : (num # num) list) =
     [x]) /\
  (maxCoverageAfterRemovingOne_insertByStart x (y::ys) =
     if FST x <= FST y then
       x::y::ys
     else
       y::maxCoverageAfterRemovingOne_insertByStart x ys)
`;

val maxCoverageAfterRemovingOne_mergeSort_def = Define `
  (maxCoverageAfterRemovingOne_mergeSort
      ([] : (num # num) list) =
     ([] : (num # num) list)) /\
  (maxCoverageAfterRemovingOne_mergeSort (x::xs) =
     maxCoverageAfterRemovingOne_insertByStart
       x (maxCoverageAfterRemovingOne_mergeSort xs))
`;

val maxCoverageAfterRemovingOne_natMax_def = new_definition (
  "maxCoverageAfterRemovingOne_natMax_def",
  ``maxCoverageAfterRemovingOne_natMax (x : num) (y : num) =
      if x < y then y else x``
);

val maxCoverageAfterRemovingOne_mergeStep_def = new_definition (
  "maxCoverageAfterRemovingOne_mergeStep_def",
  ``maxCoverageAfterRemovingOne_mergeStep
      (acc : (num # num) list) (curr : num # num) =
      case acc of
        [] => [curr]
      | h::rest =>
          if FST curr <= SND h then
            (FST h,
             maxCoverageAfterRemovingOne_natMax (SND h) (SND curr))::rest
          else
            curr::acc``
);

val maxCoverageAfterRemovingOne_merged_def = new_definition (
  "maxCoverageAfterRemovingOne_merged_def",
  ``maxCoverageAfterRemovingOne_merged
      (intervals : (num # num) list) =
      FOLDL
        maxCoverageAfterRemovingOne_mergeStep
        ([] : (num # num) list)
        (maxCoverageAfterRemovingOne_mergeSort intervals)``
);

val maxCoverageAfterRemovingOne_coverage_def = new_definition (
  "maxCoverageAfterRemovingOne_coverage_def",
  ``maxCoverageAfterRemovingOne_coverage
      (intervals : (num # num) list) =
      FOLDL
        (\acc interval.
          acc + (SND interval - FST interval))
        0
        (REVERSE (maxCoverageAfterRemovingOne_merged intervals))``
);

val maxCoverageAfterRemovingOne_coverageWithout_def = new_definition (
  "maxCoverageAfterRemovingOne_coverageWithout_def",
  ``maxCoverageAfterRemovingOne_coverageWithout
      (intervals : (num # num) list) (i : num) =
      maxCoverageAfterRemovingOne_coverage
        (maxCoverageAfterRemovingOne_eraseIdx intervals i)``
);

val maxCoverageAfterRemovingOne_def = new_definition (
  "maxCoverageAfterRemovingOne_def",
  ``maxCoverageAfterRemovingOne (intervals : (num # num) list) =
      let n = LENGTH intervals
      in
        if n <= 1 then
          0
        else
          FOLDL
            (\acc i.
              maxCoverageAfterRemovingOne_natMax
                acc
                (maxCoverageAfterRemovingOne_coverageWithout intervals i))
            0
            (COUNT_LIST n)``
);

val maxCoverageAfterRemovingOne_postcond_def = new_definition (
  "maxCoverageAfterRemovingOne_postcond_def",
  ``maxCoverageAfterRemovingOne_postcond
      (intervals : (num # num) list) (result : num) <=>
      ?i.
        i < LENGTH intervals /\
        result =
          maxCoverageAfterRemovingOne_coverageWithout intervals i /\
        !j.
          j < LENGTH intervals ==>
          maxCoverageAfterRemovingOne_coverageWithout intervals j <=
          maxCoverageAfterRemovingOne_coverageWithout intervals i``
);

val maxCoverageAfterRemovingOne_spec_satisfied =
  ``!intervals : (num # num) list.
      maxCoverageAfterRemovingOne_precond intervals ==>
      maxCoverageAfterRemovingOne_postcond
        intervals (maxCoverageAfterRemovingOne intervals)``;
