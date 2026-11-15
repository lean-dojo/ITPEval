(*
  Statement-only formalization of VERINA artifact verina_advanced_1,
  cataloged as "FindSingleNumber": the recursive program returns the sole
  integer occurring once when every other listed integer occurs twice.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val filterlist_def = new_definition (
  "filterlist_def",
  ``filterlist (x : int) (nums : int list) =
      FILTER (\y : int. y = x) nums``
);

val FindSingleNumber_counts_def = new_definition (
  "FindSingleNumber_counts_def",
  ``FindSingleNumber_counts (nums : int list) =
      MAP (\x : int. LENGTH (filterlist x nums)) nums``
);

val FindSingleNumber_precond_def = new_definition (
  "FindSingleNumber_precond_def",
  ``FindSingleNumber_precond (nums : int list) <=>
      EVERY (\count : num. count = 1 \/ count = 2)
        (FindSingleNumber_counts nums) /\
      LENGTH
        (FILTER (\count : num. count = 1)
          (FindSingleNumber_counts nums)) = 1``
);

val findUnique_def = Define`
  (findUnique (nums : int list) ([] : int list) = 0) /\
  (findUnique nums (x::xs) =
     if LENGTH (filterlist x nums) = 1 then
       x
     else
       findUnique nums xs)
`;

val FindSingleNumber_def = new_definition (
  "FindSingleNumber_def",
  ``FindSingleNumber (nums : int list) = findUnique nums nums``
);

val FindSingleNumber_postcond_def = new_definition (
  "FindSingleNumber_postcond_def",
  ``FindSingleNumber_postcond (nums : int list) (result : int) <=>
      LENGTH nums > 0 /\
      LENGTH (filterlist result nums) = 1 /\
      (!x : int.
        MEM x nums ==>
        (x = result \/ LENGTH (filterlist x nums) = 2))``
);

val FindSingleNumber_spec_satisfied =
  ``!nums : int list.
      FindSingleNumber_precond nums ==>
      FindSingleNumber_postcond nums (FindSingleNumber nums)``;
