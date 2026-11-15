(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1082910 (thousand-theorems__hol4__Q1082910), "Euler's partition theorem":
  for each natural number n, the finite sets of partitions of n into odd
  positive parts and into distinct positive parts have equal cardinality.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val card_odds_eq_card_distincts =
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
          CARD odd_partitions = CARD distinct_partitions``;
