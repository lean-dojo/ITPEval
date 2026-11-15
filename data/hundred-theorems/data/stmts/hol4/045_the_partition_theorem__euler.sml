(*
  Statement-only formalization of "The Partition Theorem (Euler)" from Hundred Theorems item
  045. For each natural number n, the finite sets of multiplicity-function partitions of n
  into distinct positive parts and into odd positive parts have equal cardinality. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val euler_partition_theorem =
  ``!n : num.
      let is_partition =
        \p : num -> num.
          (!i. p i <> 0 ==> 1 <= i /\ i <= n) /\
          SIGMA (\i. p i * i) (count (SUC n)) = n
      in
        let distinct_partitions =
          {p : num -> num |
             is_partition p /\ (!i. p i <= 1)}
        in
        let odd_partitions =
          {p : num -> num |
             is_partition p /\ (!i. p i <> 0 ==> ODD i)}
        in
          FINITE distinct_partitions /\
          FINITE odd_partitions /\
          CARD distinct_partitions = CARD odd_partitions``;
