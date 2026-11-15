(*
  Statement-only formalization of "The Partition Theorem (Euler)" from Hundred Theorems item
  045: the number of partitions into distinct parts equals the number of partitions into odd
  parts. This file contains no proof.
*)

(* ========================================================================= *)
(* Euler's partition theorem.                                                *)
(* ========================================================================= *)

let EULER_PARTITION_THEOREM = `!n:num.
  let is_partition = \p:num->num.
    (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
    nsum(1..n) (\i. p i * i) = n in
  FINITE {p:num->num | is_partition p /\ !i. p i <= 1} /\
  FINITE {p:num->num | is_partition p /\ !i. ~(p i = 0) ==> ODD i} /\
  CARD {p:num->num | is_partition p /\ !i. p i <= 1} =
  CARD {p:num->num | is_partition p /\ !i. ~(p i = 0) ==> ODD i}`;;
