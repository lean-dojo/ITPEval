(*
  Statement-only formalization of VERINA artifact verina_advanced_60,
  cataloged as "partitionEvensOdds": the executable recursive program stably
  partitions a natural-number list into its even and odd elements and satisfies
  the stated filter and parity contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory;

val partitionEvensOdds_precond_def = new_definition (
  "partitionEvensOdds_precond_def",
  ``partitionEvensOdds_precond (nums : num list) <=> T``
);

val partitionEvensOdds_helper_def = Define `
  (partitionEvensOdds_helper ([] : num list) =
     (([] : num list), ([] : num list))) /\
  (partitionEvensOdds_helper (x::xs) =
     let result = partitionEvensOdds_helper xs
     in
       if x MOD 2 = 0 then
         (x::FST result, SND result)
       else
         (FST result, x::SND result))
`;

val partitionEvensOdds_def = new_definition (
  "partitionEvensOdds_def",
  ``partitionEvensOdds (nums : num list) =
      partitionEvensOdds_helper nums``
);

val partitionEvensOdds_postcond_def = new_definition (
  "partitionEvensOdds_postcond_def",
  ``partitionEvensOdds_postcond
      (nums : num list) (result : num list # num list) <=>
      FST result ++ SND result =
        FILTER (\n : num. n MOD 2 = 0) nums ++
        FILTER (\n : num. n MOD 2 = 1) nums /\
      EVERY (\n : num. n MOD 2 = 0) (FST result) /\
      EVERY (\n : num. n MOD 2 = 1) (SND result)``
);

val partitionEvensOdds_spec_satisfied =
  ``!nums : num list.
      partitionEvensOdds_precond nums ==>
      partitionEvensOdds_postcond
        nums (partitionEvensOdds nums)``;
