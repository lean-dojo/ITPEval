(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_tree_of_arrayqtvc: the cumulative-tree
  construction verification condition for recursive midpoint calls and the
  resulting half-open integer range-sum tree invariant. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  sumrange_tree_indexes =
    SumrangeTreeIndexes int int int
End

val sumrange_tree_low_def = Define `
  sumrange_tree_low (SumrangeTreeIndexes low high isum) = low`;

val sumrange_tree_high_def = Define `
  sumrange_tree_high (SumrangeTreeIndexes low high isum) = high`;

val sumrange_tree_isum_def = Define `
  sumrange_tree_isum (SumrangeTreeIndexes low high isum) = isum`;

Datatype:
  sumrange_tree =
    SumrangeTreeLeaf sumrange_tree_indexes
  | SumrangeTreeNode
      sumrange_tree_indexes sumrange_tree sumrange_tree
End

val sumrange_tree_indexes_of_def = Define `
  (sumrange_tree_indexes_of (SumrangeTreeLeaf ind) = ind) /\
  (sumrange_tree_indexes_of (SumrangeTreeNode ind l r) = ind)`;

val sumrange_tree_to_num_def = Define `
  sumrange_tree_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sumrange_tree_get_def = Define `
  sumrange_tree_get (a : int list) (i : int) =
    if (0 : int) <= i /\
       sumrange_tree_to_num i < LENGTH a then
      EL (sumrange_tree_to_num i) a
    else
      (0 : int)`;

val sumrange_tree_sum_from_def = Define `
  (sumrange_tree_sum_from
      (a : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_tree_sum_from a start (SUC count) =
     EL start a +
     sumrange_tree_sum_from a (SUC start) count)`;

val sumrange_tree_sum_def = Define `
  sumrange_tree_sum
      (a : int list) (i : int) (j : int) =
    sumrange_tree_sum_from
      a
      (sumrange_tree_to_num i)
      (sumrange_tree_to_num (j - i))`;

val sumrange_tree_is_indexes_for_def = Define `
  sumrange_tree_is_indexes_for
      ind (a : int list) (i : int) (j : int) <=>
    sumrange_tree_low ind = i /\
    sumrange_tree_high ind = j /\
    (0 : int) <= i /\
    i < j /\
    j <= &(LENGTH a) /\
    sumrange_tree_isum ind = sumrange_tree_sum a i j`;

val sumrange_tree_is_tree_for_def = Define `
  (sumrange_tree_is_tree_for
      (SumrangeTreeLeaf ind) (a : int list) (i : int) (j : int) <=>
     sumrange_tree_is_indexes_for ind a i j /\
     j = i + (1 : int)) /\
  (sumrange_tree_is_tree_for
      (SumrangeTreeNode ind l r) a i j <=>
     sumrange_tree_is_indexes_for ind a i j /\
     i = sumrange_tree_low (sumrange_tree_indexes_of l) /\
     j = sumrange_tree_high (sumrange_tree_indexes_of r) /\
     (let m = sumrange_tree_high (sumrange_tree_indexes_of l)
      in
        m = sumrange_tree_low (sumrange_tree_indexes_of r) /\
        i < m /\
        m < j /\
        m = (i + j) quot (2 : int) /\
        sumrange_tree_is_tree_for l a i m /\
        sumrange_tree_is_tree_for r a m j))`;

val sumrange_CumulativeTree_tree_of_arrayqtvc_statement =
  ``!(i : int) (j : int) (a : int list).
      (0 : int) <= i ==>
      i < j ==>
      j <= &(LENGTH a) ==>
      let o1 = i + (1 : int)
      in
        (if o1 = j then
           (0 : int) <= i /\ i < &(LENGTH a)
         else
           ~((2 : int) = (0 : int)) /\
           (let m = (i + j) quot (2 : int)
            in
              (((0 : int) <= j - i /\ m - i < j - i) /\
               (0 : int) <= i /\
               i < m /\
               m <= &(LENGTH a)) /\
              (!l : sumrange_tree.
                 sumrange_tree_is_tree_for l a i m ==>
                 ((0 : int) <= j - i /\ j - m < j - i) /\
                 (0 : int) <= m /\
                 m < j /\
                 j <= &(LENGTH a)))) /\
        (!result : sumrange_tree.
           (if o1 = j then
              result =
                SumrangeTreeLeaf
                  (SumrangeTreeIndexes
                    i j (sumrange_tree_get a i))
            else
              let m = (i + j) quot (2 : int)
              in
                ?l : sumrange_tree.
                  sumrange_tree_is_tree_for l a i m /\
                  ?r : sumrange_tree.
                    sumrange_tree_is_tree_for r a m j /\
                    result =
                      SumrangeTreeNode
                        (SumrangeTreeIndexes
                          i j
                          (sumrange_tree_isum
                             (sumrange_tree_indexes_of l) +
                           sumrange_tree_isum
                             (sumrange_tree_indexes_of r)))
                        l r)
           ==>
           sumrange_tree_is_tree_for result a i j)``;
