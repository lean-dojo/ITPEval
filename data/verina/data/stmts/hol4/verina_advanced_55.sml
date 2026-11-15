(*
  Statement-only formalization of VERINA artifact verina_advanced_55,
  cataloged as "mostFrequent": the executable frequency-map fold returns the
  first integer in a non-empty input list having maximum occurrence count.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val mostFrequent_precond_def = new_definition (
  "mostFrequent_precond_def",
  ``mostFrequent_precond (xs : int list) <=>
      xs <> []``
);

val mostFrequent_countMapInsert_def = Define `
  (mostFrequent_countMapInsert
      (x : int) ([] : (int # num) list) =
     [(x, 1)]) /\
  (mostFrequent_countMapInsert
      x ((key, count)::rest) =
     if x = key then
       (key, count + 1)::rest
     else
       (key, count)::mostFrequent_countMapInsert x rest)
`;

val countMap_def = new_definition (
  "countMap_def",
  ``countMap (xs : int list) =
      FOLDL
        (\m x. mostFrequent_countMapInsert x m)
        ([] : (int # num) list)
        xs``
);

val getMaxFrequency_def = new_definition (
  "getMaxFrequency_def",
  ``getMaxFrequency (m : (int # num) list) =
      FOLDL
        (\acc entry.
           if SND entry > acc then SND entry else acc)
        0
        m``
);

val getCandidates_def = new_definition (
  "getCandidates_def",
  ``getCandidates
      (m : (int # num) list) (maxFreq : num) =
      MAP FST (FILTER (\entry. SND entry = maxFreq) m)``
);

val getFirstWithFreq_def = Define `
  (getFirstWithFreq
      ([] : int list) (candidates : int list) =
     (0 : int)) /\
  (getFirstWithFreq
      (x::xs) candidates =
     if MEM x candidates then
       x
     else
       getFirstWithFreq xs candidates)
`;

val mostFrequent_def = new_definition (
  "mostFrequent_def",
  ``mostFrequent (xs : int list) =
      let freqMap = countMap xs in
      let maxF = getMaxFrequency freqMap in
      let candidates = getCandidates freqMap maxF in
        getFirstWithFreq xs candidates``
);

val mostFrequent_count_def = new_definition (
  "mostFrequent_count_def",
  ``mostFrequent_count (xs : int list) (x : int) =
      LENGTH (FILTER (\y : int. y = x) xs)``
);

val mostFrequent_postcond_def = new_definition (
  "mostFrequent_postcond_def",
  ``mostFrequent_postcond
      (xs : int list) (result : int) <=>
      MEM result xs /\
      EVERY
        (\x : int.
           mostFrequent_count xs x <=
           mostFrequent_count xs result)
        xs /\
      (case
         FILTER
           (\x : int.
              mostFrequent_count xs x =
              mostFrequent_count xs result)
           xs
       of
         [] => NONE
       | x::rest => SOME x) = SOME result``
);

val mostFrequent_spec_satisfied =
  ``!xs : int list.
      mostFrequent_precond xs ==>
      mostFrequent_postcond xs (mostFrequent xs)``;
