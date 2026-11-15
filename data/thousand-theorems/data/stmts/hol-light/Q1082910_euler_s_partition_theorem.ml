(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1082910,
  "Euler's partition theorem": for every natural number, the number of its
  partitions into odd parts equals the number of its partitions into distinct
  parts. This file contains no proof.
*)

let euler_partition_theorem = `!n:num.
  let is_partition = \p:num->num.
    (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
    nsum(1..n) (\i. p i * i) = n in
  FINITE {p:num->num |
    is_partition p /\ !i. ~(p i = 0) ==> ODD i} /\
  FINITE {p:num->num |
    is_partition p /\ !i. p i <= 1} /\
  CARD {p:num->num |
    is_partition p /\ !i. ~(p i = 0) ==> ODD i} =
  CARD {p:num->num |
    is_partition p /\ !i. p i <= 1}`;;
