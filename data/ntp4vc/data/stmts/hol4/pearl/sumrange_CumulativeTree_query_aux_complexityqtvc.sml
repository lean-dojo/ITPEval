(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_query_aux_complexityqtvc: the auxiliary
  cumulative-tree range-query verification condition, preserving the
  half-open range sum and its depth-based credit bound. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  sumrange_query_indexes =
    SumrangeQueryIndexes int int int
End

val sumrange_query_low_def = Define `
  sumrange_query_low (SumrangeQueryIndexes low high isum) = low`;

val sumrange_query_high_def = Define `
  sumrange_query_high (SumrangeQueryIndexes low high isum) = high`;

val sumrange_query_isum_def = Define `
  sumrange_query_isum (SumrangeQueryIndexes low high isum) = isum`;

Datatype:
  sumrange_query_tree =
    SumrangeQueryLeaf sumrange_query_indexes
  | SumrangeQueryNode
      sumrange_query_indexes sumrange_query_tree sumrange_query_tree
End

val sumrange_query_indexes_of_def = Define `
  (sumrange_query_indexes_of (SumrangeQueryLeaf ind) = ind) /\
  (sumrange_query_indexes_of (SumrangeQueryNode ind l r) = ind)`;

val sumrange_query_to_num_def = Define `
  sumrange_query_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sumrange_query_sum_from_def = Define `
  (sumrange_query_sum_from
      (a : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_query_sum_from a start (SUC count) =
     EL start a +
     sumrange_query_sum_from a (SUC start) count)`;

val sumrange_query_sum_def = Define `
  sumrange_query_sum
      (a : int list) (i : int) (j : int) =
    sumrange_query_sum_from
      a
      (sumrange_query_to_num i)
      (sumrange_query_to_num (j - i))`;

val sumrange_query_is_indexes_for_def = Define `
  sumrange_query_is_indexes_for
      ind (a : int list) (i : int) (j : int) <=>
    sumrange_query_low ind = i /\
    sumrange_query_high ind = j /\
    (0 : int) <= i /\
    i < j /\
    j <= &(LENGTH a) /\
    sumrange_query_isum ind = sumrange_query_sum a i j`;

val sumrange_query_is_tree_for_def = Define `
  (sumrange_query_is_tree_for
      (SumrangeQueryLeaf ind) (a : int list) (i : int) (j : int) <=>
     sumrange_query_is_indexes_for ind a i j /\
     j = i + (1 : int)) /\
  (sumrange_query_is_tree_for
      (SumrangeQueryNode ind l r) a i j <=>
     sumrange_query_is_indexes_for ind a i j /\
     i = sumrange_query_low (sumrange_query_indexes_of l) /\
     j = sumrange_query_high (sumrange_query_indexes_of r) /\
     (let m = sumrange_query_high (sumrange_query_indexes_of l) in
        m = sumrange_query_low (sumrange_query_indexes_of r) /\
        i < m /\
        m < j /\
        m = (i + j) quot (2 : int) /\
        sumrange_query_is_tree_for l a i m /\
        sumrange_query_is_tree_for r a m j))`;

val sumrange_query_depth_def = Define `
  (sumrange_query_depth (SumrangeQueryLeaf ind) = (1 : int)) /\
  (sumrange_query_depth (SumrangeQueryNode ind l r) =
     (1 : int) +
     if sumrange_query_depth l < sumrange_query_depth r
     then sumrange_query_depth r
     else sumrange_query_depth l)`;

val sumrange_query_bound_def = Define `
  sumrange_query_bound t (i : int) (j : int) =
    if i = sumrange_query_low (sumrange_query_indexes_of t) /\
       j = sumrange_query_high (sumrange_query_indexes_of t)
    then (1 : int)
    else if
      i = sumrange_query_low (sumrange_query_indexes_of t) \/
      j = sumrange_query_high (sumrange_query_indexes_of t)
    then (2 : int) * sumrange_query_depth t
    else (4 : int) * sumrange_query_depth t`;

val sumrange_query_is_child_def = Define `
  (sumrange_query_is_child (SumrangeQueryLeaf ind) child <=> F) /\
  (sumrange_query_is_child (SumrangeQueryNode ind l r) child <=>
     l = child \/ r = child)`;

val sumrange_CumulativeTree_query_aux_complexityqtvc_statement =
  ``!(t : sumrange_query_tree)
      (a : int list)
      (i : int)
      (j : int)
      (c : int).
      sumrange_query_is_tree_for
        t a
        (sumrange_query_low (sumrange_query_indexes_of t))
        (sumrange_query_high (sumrange_query_indexes_of t)) /\
      (0 : int) <=
        sumrange_query_low (sumrange_query_indexes_of t) /\
      sumrange_query_low (sumrange_query_indexes_of t) <= i /\
      i < j /\
      j <= sumrange_query_high (sumrange_query_indexes_of t) /\
      sumrange_query_high (sumrange_query_indexes_of t) <= &(LENGTH a)
      ==>
      case t of
        SumrangeQueryLeaf ind =>
          c + (1 : int) - c <= sumrange_query_bound t i j /\
          sumrange_query_isum ind = sumrange_query_sum a i j
      | SumrangeQueryNode ind l r =>
          !o1 : bool.
            (if i = sumrange_query_low ind
             then
               o1 =
                 (if j = sumrange_query_high ind then T else F)
             else o1 = F)
            ==>
            if o1 = T then
              c + (1 : int) - c <= sumrange_query_bound t i j /\
              sumrange_query_isum ind = sumrange_query_sum a i j
            else
              let m =
                sumrange_query_high (sumrange_query_indexes_of l)
              in
                if j <= m then
                  (sumrange_query_is_child t l /\
                   sumrange_query_is_tree_for
                     l a
                     (sumrange_query_low
                       (sumrange_query_indexes_of l))
                     (sumrange_query_high
                       (sumrange_query_indexes_of l)) /\
                   (0 : int) <=
                     sumrange_query_low
                       (sumrange_query_indexes_of l) /\
                   sumrange_query_low
                     (sumrange_query_indexes_of l) <= i /\
                   i < j /\
                   j <=
                     sumrange_query_high
                       (sumrange_query_indexes_of l) /\
                   sumrange_query_high
                     (sumrange_query_indexes_of l) <= &(LENGTH a)) /\
                  (!c1 : int.
                    c1 - (c + (1 : int)) <=
                      sumrange_query_bound l i j
                    ==>
                    c1 - c <= sumrange_query_bound t i j)
                else if m <= i then
                  (sumrange_query_is_child t r /\
                   sumrange_query_is_tree_for
                     r a
                     (sumrange_query_low
                       (sumrange_query_indexes_of r))
                     (sumrange_query_high
                       (sumrange_query_indexes_of r)) /\
                   (0 : int) <=
                     sumrange_query_low
                       (sumrange_query_indexes_of r) /\
                   sumrange_query_low
                     (sumrange_query_indexes_of r) <= i /\
                   i < j /\
                   j <=
                     sumrange_query_high
                       (sumrange_query_indexes_of r) /\
                   sumrange_query_high
                     (sumrange_query_indexes_of r) <= &(LENGTH a)) /\
                  (!c1 : int.
                    c1 - (c + (1 : int)) <=
                      sumrange_query_bound r i j
                    ==>
                    c1 - c <= sumrange_query_bound t i j)
                else
                  (sumrange_query_is_child t r /\
                   sumrange_query_is_tree_for
                     r a
                     (sumrange_query_low
                       (sumrange_query_indexes_of r))
                     (sumrange_query_high
                       (sumrange_query_indexes_of r)) /\
                   (0 : int) <=
                     sumrange_query_low
                       (sumrange_query_indexes_of r) /\
                   sumrange_query_low
                     (sumrange_query_indexes_of r) <= m /\
                   m < j /\
                   j <=
                     sumrange_query_high
                       (sumrange_query_indexes_of r) /\
                   sumrange_query_high
                     (sumrange_query_indexes_of r) <= &(LENGTH a)) /\
                  (!c1 : int.
                    c1 - (c + (1 : int)) <=
                      sumrange_query_bound r m j
                    ==>
                    (sumrange_query_is_child t l /\
                     sumrange_query_is_tree_for
                       l a
                       (sumrange_query_low
                         (sumrange_query_indexes_of l))
                       (sumrange_query_high
                         (sumrange_query_indexes_of l)) /\
                     (0 : int) <=
                       sumrange_query_low
                         (sumrange_query_indexes_of l) /\
                     sumrange_query_low
                       (sumrange_query_indexes_of l) <= i /\
                     i < m /\
                     m <=
                       sumrange_query_high
                         (sumrange_query_indexes_of l) /\
                     sumrange_query_high
                       (sumrange_query_indexes_of l) <= &(LENGTH a)) /\
                    (!c2 : int.
                      c2 - c1 <= sumrange_query_bound l i m
                      ==>
                      c2 - c <= sumrange_query_bound t i j /\
                      sumrange_query_sum a i m +
                        sumrange_query_sum a m j =
                        sumrange_query_sum a i j))``;
