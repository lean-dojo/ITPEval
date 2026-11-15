(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b1:
  for any two partitions of a nine-element set, two distinct elements have
  the same block size in both partitions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val putnam_1995_b1 =
  ``let base = count 9
    in
    let is_partition =
      \P : num set set.
        (!B : num set.
           B IN P ==> B <> {} /\ B SUBSET base) /\
        BIGUNION P = base /\
        (!A B : num set.
           A IN P /\ B IN P /\ A <> B ==> DISJOINT A B)
    in
    let block_size =
      \P : num set set.
      \x : num.
        CARD
          {y : num |
             ?B : num set.
               B IN P /\ x IN B /\ y IN B}
    in
      !P Q : num set set.
        is_partition P /\ is_partition Q
        ==>
        ?x y : num.
          x IN base /\
          y IN base /\
          x <> y /\
          block_size P x = block_size P y /\
          block_size Q x = block_size Q y``;
