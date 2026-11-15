(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_auxqtvc: the cumulative-tree auxiliary
  update verification condition, preserving recursive-call obligations,
  updated half-open range sums, and tree bounds. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  sumrange_update_indexes =
    SumrangeUpdateIndexes int int int
End

val sumrange_update_low_def = Define `
  sumrange_update_low (SumrangeUpdateIndexes low high isum) = low`;

val sumrange_update_high_def = Define `
  sumrange_update_high (SumrangeUpdateIndexes low high isum) = high`;

val sumrange_update_isum_def = Define `
  sumrange_update_isum (SumrangeUpdateIndexes low high isum) = isum`;

Datatype:
  sumrange_update_tree =
    SumrangeUpdateLeaf sumrange_update_indexes
  | SumrangeUpdateNode
      sumrange_update_indexes sumrange_update_tree sumrange_update_tree
End

val sumrange_update_indexes_of_def = Define `
  (sumrange_update_indexes_of (SumrangeUpdateLeaf ind) = ind) /\
  (sumrange_update_indexes_of (SumrangeUpdateNode ind l r) = ind)`;

val sumrange_update_to_num_def = Define `
  sumrange_update_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sumrange_update_get_def = Define `
  sumrange_update_get (a : int list) (i : int) =
    EL (sumrange_update_to_num i) a`;

val sumrange_update_array_def = Define `
  sumrange_update_array
      (a : int list) (i : int) (v : int) =
    LUPDATE v (sumrange_update_to_num i) a`;

val sumrange_update_sum_from_def = Define `
  (sumrange_update_sum_from
      (a : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_update_sum_from a start (SUC count) =
     EL start a +
     sumrange_update_sum_from a (SUC start) count)`;

val sumrange_update_sum_def = Define `
  sumrange_update_sum
      (a : int list) (i : int) (j : int) =
    sumrange_update_sum_from
      a
      (sumrange_update_to_num i)
      (sumrange_update_to_num (j - i))`;

val sumrange_update_is_indexes_for_def = Define `
  sumrange_update_is_indexes_for
      ind (a : int list) (i : int) (j : int) <=>
    sumrange_update_low ind = i /\
    sumrange_update_high ind = j /\
    (0 : int) <= i /\
    i < j /\
    j <= &(LENGTH a) /\
    sumrange_update_isum ind = sumrange_update_sum a i j`;

val sumrange_update_is_tree_for_def = Define `
  (sumrange_update_is_tree_for
      (SumrangeUpdateLeaf ind)
      (a : int list) (i : int) (j : int) <=>
     sumrange_update_is_indexes_for ind a i j /\
     j = i + (1 : int)) /\
  (sumrange_update_is_tree_for
      (SumrangeUpdateNode ind l r) a i j <=>
     sumrange_update_is_indexes_for ind a i j /\
     i = sumrange_update_low (sumrange_update_indexes_of l) /\
     j = sumrange_update_high (sumrange_update_indexes_of r) /\
     (let m =
        sumrange_update_high (sumrange_update_indexes_of l)
      in
        m = sumrange_update_low (sumrange_update_indexes_of r) /\
        i < m /\
        m < j /\
        m = (i + j) quot (2 : int) /\
        sumrange_update_is_tree_for l a i m /\
        sumrange_update_is_tree_for r a m j))`;

val sumrange_update_is_child_def = Define `
  (sumrange_update_is_child
      (SumrangeUpdateLeaf ind) child <=> F) /\
  (sumrange_update_is_child
      (SumrangeUpdateNode ind l r) child <=>
     l = child \/ r = child)`;

val sumrange_CumulativeTree_update_auxqtvc_statement =
  ``!(t : sumrange_update_tree)
      (a : int list)
      (i : int)
      (v : int).
      sumrange_update_is_tree_for
        t a
        (sumrange_update_low (sumrange_update_indexes_of t))
        (sumrange_update_high (sumrange_update_indexes_of t)) /\
      sumrange_update_low (sumrange_update_indexes_of t) <= i /\
      i < sumrange_update_high (sumrange_update_indexes_of t)
      ==>
      (case t of
         SumrangeUpdateLeaf ind => T
       | SumrangeUpdateNode ind l r =>
           if i <
              sumrange_update_high (sumrange_update_indexes_of l)
           then
             sumrange_update_is_child t l /\
             sumrange_update_is_tree_for
               l a
               (sumrange_update_low (sumrange_update_indexes_of l))
               (sumrange_update_high (sumrange_update_indexes_of l)) /\
             sumrange_update_low (sumrange_update_indexes_of l) <= i /\
             i < sumrange_update_high (sumrange_update_indexes_of l)
           else
             sumrange_update_is_child t r /\
             sumrange_update_is_tree_for
               r a
               (sumrange_update_low (sumrange_update_indexes_of r))
               (sumrange_update_high (sumrange_update_indexes_of r)) /\
             sumrange_update_low (sumrange_update_indexes_of r) <= i /\
             i < sumrange_update_high (sumrange_update_indexes_of r)) /\
      (!(t' : sumrange_update_tree) (delta : int).
        (case t of
           SumrangeUpdateLeaf ind =>
             t' =
               SumrangeUpdateLeaf
                 (SumrangeUpdateIndexes
                   (sumrange_update_low ind)
                   (sumrange_update_high ind)
                   v) /\
             delta = v - sumrange_update_isum ind
         | SumrangeUpdateNode ind l r =>
             if i <
                sumrange_update_high (sumrange_update_indexes_of l)
             then
               ?t'1 : sumrange_update_tree.
                 (sumrange_update_low
                    (sumrange_update_indexes_of t'1) =
                    sumrange_update_low
                      (sumrange_update_indexes_of l) /\
                  sumrange_update_high
                    (sumrange_update_indexes_of t'1) =
                    sumrange_update_high
                      (sumrange_update_indexes_of l) /\
                  sumrange_update_is_tree_for
                    t'1 (sumrange_update_array a i v)
                    (sumrange_update_low
                      (sumrange_update_indexes_of t'1))
                    (sumrange_update_high
                      (sumrange_update_indexes_of t'1))) /\
                 t' =
                   SumrangeUpdateNode
                     (SumrangeUpdateIndexes
                       (sumrange_update_low ind)
                       (sumrange_update_high ind)
                       (sumrange_update_isum ind +
                        (v - sumrange_update_get a i)))
                     t'1 r /\
                 delta = v - sumrange_update_get a i
             else
               ?t'1 : sumrange_update_tree.
                 (sumrange_update_low
                    (sumrange_update_indexes_of t'1) =
                    sumrange_update_low
                      (sumrange_update_indexes_of r) /\
                  sumrange_update_high
                    (sumrange_update_indexes_of t'1) =
                    sumrange_update_high
                      (sumrange_update_indexes_of r) /\
                  sumrange_update_is_tree_for
                    t'1 (sumrange_update_array a i v)
                    (sumrange_update_low
                      (sumrange_update_indexes_of t'1))
                    (sumrange_update_high
                      (sumrange_update_indexes_of t'1))) /\
                 t' =
                   SumrangeUpdateNode
                     (SumrangeUpdateIndexes
                       (sumrange_update_low ind)
                       (sumrange_update_high ind)
                       (sumrange_update_isum ind +
                        (v - sumrange_update_get a i)))
                     l t'1 /\
                 delta = v - sumrange_update_get a i)
        ==>
        delta = v - sumrange_update_get a i /\
        sumrange_update_low (sumrange_update_indexes_of t') =
          sumrange_update_low (sumrange_update_indexes_of t) /\
        sumrange_update_high (sumrange_update_indexes_of t') =
          sumrange_update_high (sumrange_update_indexes_of t) /\
        sumrange_update_is_tree_for
          t' (sumrange_update_array a i v)
          (sumrange_update_low (sumrange_update_indexes_of t'))
          (sumrange_update_high (sumrange_update_indexes_of t')))``;
