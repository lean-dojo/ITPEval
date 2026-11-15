(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5566491 (thousand-theorems__hol4__Q5566491), "Glaisher's theorem":
  for positive m, partitions of n into parts not divisible by m are
  equinumerous with partitions in which every part occurs fewer than m times.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val glaisher_s_theorem =
  ``!n m : num.
      0 < m
      ==>
      let is_partition =
        \p : num -> num.
          (!i. p i <> 0 ==> 1 <= i /\ i <= n) /\
          SIGMA (\i. p i * i) (count (SUC n)) = n
      in
        let nondivisible_partitions =
          {p : num -> num |
             is_partition p /\
             (!i. p i <> 0 ==> ~(divides m i))}
        in
          let multiplicity_restricted_partitions =
            {p : num -> num |
               is_partition p /\ (!i. p i < m)}
          in
            FINITE nondivisible_partitions /\
            FINITE multiplicity_restricted_partitions /\
            CARD nondivisible_partitions =
              CARD multiplicity_restricted_partitions``;
