(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5566491,
  "Glaisher's theorem": for every natural number n and positive m, the number
  of partitions of n into parts not divisible by m equals the number in which
  every occurring part has multiplicity less than m. This file contains no
  proof.
*)

let glaisher_theorem = `!n m:num.
  0 < m ==>
  let is_partition = \p:num->num.
    (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
    nsum(1..n) (\i. p i * i) = n in
  let restricted = {p:num->num |
    is_partition p /\ !i. ~(p i = 0) ==> ~(m divides i)} in
  let count_restricted = {p:num->num |
    is_partition p /\ !i. ~(p i = 0) ==> p i < m} in
  FINITE restricted /\
  FINITE count_restricted /\
  CARD restricted = CARD count_restricted`;;
