(*
  Statement-only formalization of VERINA artifact verina_advanced_47,
  cataloged as "mergeIntervals": the executable program stably sorts integer
  intervals by starting point and merges overlapping intervals; its result
  satisfies the stated coverage, separation, endpoint, and no-gap checks.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pairTheory;

val mergeIntervals_precond_def = new_definition (
  "mergeIntervals_precond_def",
  ``mergeIntervals_precond
      (intervals : (int # int) list) <=>
      EVERY (\interval. FST interval <= SND interval) intervals``
);

val mergeIntervals_insert_def = Define `
  (mergeIntervals_insert
      (x : int # int) ([] : (int # int) list) =
     [x]) /\
  (mergeIntervals_insert x (y::ys) =
     if FST x <= FST y then
       x::y::ys
     else
       y::mergeIntervals_insert x ys)
`;

val mergeIntervals_sort_def = Define `
  (mergeIntervals_sort
      ([] : (int # int) list) =
     ([] : (int # int) list)) /\
  (mergeIntervals_sort (x::xs) =
     mergeIntervals_insert x (mergeIntervals_sort xs))
`;

val mergeIntervals_intMax_def = new_definition (
  "mergeIntervals_intMax_def",
  ``mergeIntervals_intMax (x : int) (y : int) =
      if x < y then y else x``
);

val mergeIntervals_merge_def = Define `
  (mergeIntervals_merge
      ([] : (int # int) list) (acc : (int # int) list) =
     REVERSE acc) /\
  (mergeIntervals_merge (x::xs) [] =
     mergeIntervals_merge xs [x]) /\
  (mergeIntervals_merge (x::xs) (previous::accTail) =
     if FST x <= SND previous then
       mergeIntervals_merge
         xs
         ((FST previous,
           mergeIntervals_intMax (SND previous) (SND x))::accTail)
     else
       mergeIntervals_merge xs (x::previous::accTail))
`;

val mergeIntervals_def = new_definition (
  "mergeIntervals_def",
  ``mergeIntervals (intervals : (int # int) list) =
      mergeIntervals_merge (mergeIntervals_sort intervals) []``
);

val mergeIntervals_noOverlap_def = Define `
  (mergeIntervals_noOverlap
      ([] : (int # int) list) = T) /\
  (mergeIntervals_noOverlap [x] = T) /\
  (mergeIntervals_noOverlap (x::y::rest) =
     (SND x < FST y /\
      mergeIntervals_noOverlap (y::rest)))
`;

val mergeIntervals_covered_def = new_definition (
  "mergeIntervals_covered_def",
  ``mergeIntervals_covered
      (intervals : (int # int) list)
      (result : (int # int) list) <=>
      EVERY
        (\interval.
           EXISTS
             (\merged.
                FST merged <= FST interval /\
                SND interval <= SND merged)
             result)
        intervals``
);

val mergeIntervals_resultBounded_def = new_definition (
  "mergeIntervals_resultBounded_def",
  ``mergeIntervals_resultBounded
      (intervals : (int # int) list)
      (result : (int # int) list) <=>
      EVERY
        (\merged.
           EXISTS
             (\interval. FST interval = FST merged)
             intervals /\
           EXISTS
             (\interval. SND interval = SND merged)
             intervals)
        result``
);

val mergeIntervals_noSpuriousMerge_def = new_definition (
  "mergeIntervals_noSpuriousMerge_def",
  ``mergeIntervals_noSpuriousMerge
      (intervals : (int # int) list)
      (result : (int # int) list) <=>
      EVERY
        (\merged.
           EVERY
             (\interval.
                FST interval = FST merged \/
                EXISTS
                  (\earlier.
                     FST merged <= FST earlier /\
                     SND earlier <= SND merged /\
                     FST earlier < FST interval /\
                     FST interval <= SND earlier)
                  intervals)
             (FILTER
               (\interval.
                  FST merged <= FST interval /\
                  SND interval <= SND merged)
               intervals))
        result``
);

val mergeIntervals_postcond_def = new_definition (
  "mergeIntervals_postcond_def",
  ``mergeIntervals_postcond
      (intervals : (int # int) list)
      (result : (int # int) list) <=>
      mergeIntervals_covered intervals result /\
      mergeIntervals_noOverlap result /\
      mergeIntervals_resultBounded intervals result /\
      mergeIntervals_noSpuriousMerge intervals result``
);

val mergeIntervals_spec_satisfied =
  ``!intervals : (int # int) list.
      mergeIntervals_precond intervals ==>
      mergeIntervals_postcond
        intervals (mergeIntervals intervals)``;
