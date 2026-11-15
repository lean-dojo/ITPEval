(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_76,
  catalog title "topKFrequent": the executable frequency-counting and stable
  descending insertion-sort program returns the requested most-frequent
  integers under its distinct-element precondition. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val topKFrequent_eraseDups_def = new_definition (
  "topKFrequent_eraseDups_def",
  ``topKFrequent_eraseDups (nums : int list) =
      FOLDL
        (\seen : int list. \x : int.
           if MEM x seen then seen else seen ++ [x])
        ([] : int list)
        nums``
);

val topKFrequent_precond_def = new_definition (
  "topKFrequent_precond_def",
  ``topKFrequent_precond (nums : int list) (k : num) <=>
      k <= LENGTH (topKFrequent_eraseDups nums)``
);

val topKFrequent_freqStep_def = new_definition (
  "topKFrequent_freqStep_def",
  ``topKFrequent_freqStep
      (acc : (int # num) list) (n : int) =
      if MEM n (MAP FST acc) then
        MAP
          (\entry : int # num.
             if FST entry = n then
               (FST entry, SND entry + 1)
             else
               entry)
          acc
      else
        acc ++ [(n, 1)]``
);

val topKFrequent_freqList_def = new_definition (
  "topKFrequent_freqList_def",
  ``topKFrequent_freqList (nums : int list) =
      FOLDL topKFrequent_freqStep
        ([] : (int # num) list) nums``
);

val topKFrequent_insertSorted_def = Define `
  (topKFrequent_insertSorted
      (pair : int # num) ([] : (int # num) list) =
     [pair]) /\
  (topKFrequent_insertSorted
      pair (entry::rest) =
     if SND pair > SND entry then
       pair::entry::rest
     else
       entry::topKFrequent_insertSorted pair rest)
`;

val topKFrequent_sorted_def = new_definition (
  "topKFrequent_sorted_def",
  ``topKFrequent_sorted (nums : int list) =
      FOLDL
        (\acc : (int # num) list. \pair : int # num.
           topKFrequent_insertSorted pair acc)
        ([] : (int # num) list)
        (topKFrequent_freqList nums)``
);

val topKFrequent_def = new_definition (
  "topKFrequent_def",
  ``topKFrequent (nums : int list) (k : num) =
      MAP FST (TAKE k (topKFrequent_sorted nums))``
);

val topKFrequent_count_def = new_definition (
  "topKFrequent_count_def",
  ``topKFrequent_count (nums : int list) (x : int) =
      LENGTH (FILTER (\y : int. y = x) nums)``
);

val topKFrequent_zipIdxFrom_def = Define `
  (topKFrequent_zipIdxFrom
      (index : num) ([] : int list) =
     ([] : (int # num) list)) /\
  (topKFrequent_zipIdxFrom
      index (x::xs) =
     (x, index)::topKFrequent_zipIdxFrom (SUC index) xs)
`;

val topKFrequent_zipIdx_def = new_definition (
  "topKFrequent_zipIdx_def",
  ``topKFrequent_zipIdx (xs : int list) =
      topKFrequent_zipIdxFrom 0 xs``
);

val topKFrequent_ordered_def = Define `
  (topKFrequent_ordered
      (nums : int list) ([] : (int # num) list) =
     T) /\
  (topKFrequent_ordered
      nums (entry::rest) =
     EVERY
       (\later : int # num.
          SND entry < SND later ==>
          topKFrequent_count nums (FST later) <=
          topKFrequent_count nums (FST entry))
       rest /\
     topKFrequent_ordered nums rest)
`;

val topKFrequent_postcond_def = new_definition (
  "topKFrequent_postcond_def",
  ``topKFrequent_postcond
      (nums : int list) (k : num) (result : int list) <=>
      LENGTH result = k /\
      EVERY (\x : int. MEM x nums) result /\
      ALL_DISTINCT result /\
      EVERY
        (\x : int.
           EVERY
             (\y : int.
                MEM y result \/
                topKFrequent_count nums y <=
                topKFrequent_count nums x)
             nums)
        result /\
      topKFrequent_ordered nums (topKFrequent_zipIdx result)``
);

val topKFrequent_spec_satisfied =
  ``!(nums : int list) (k : num).
      topKFrequent_precond nums k ==>
      topKFrequent_postcond
        nums k (topKFrequent nums k)``;
