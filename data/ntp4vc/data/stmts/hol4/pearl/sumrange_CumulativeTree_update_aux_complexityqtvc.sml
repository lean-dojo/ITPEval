(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_aux_complexityqtvc: the cumulative-tree
  auxiliary update verification condition, preserving the updated half-open
  range sums, tree bounds, and the depth-based credit bound. This file
  contains no proof.
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

val sumrange_update_depth_def = Define `
  (sumrange_update_depth (SumrangeUpdateLeaf ind) = (1 : int)) /\
  (sumrange_update_depth (SumrangeUpdateNode ind l r) =
     (1 : int) +
     if sumrange_update_depth l < sumrange_update_depth r
     then sumrange_update_depth r
     else sumrange_update_depth l)`;

val sumrange_update_is_child_def = Define `
  (sumrange_update_is_child
      (SumrangeUpdateLeaf ind) child <=> F) /\
  (sumrange_update_is_child
      (SumrangeUpdateNode ind l r) child <=>
     l = child \/ r = child)`;

val sumrange_update_changed_indexes_def = Define `
  sumrange_update_changed_indexes
      ind (a : int list) (i : int) (v : int) =
    SumrangeUpdateIndexes
      (sumrange_update_low ind)
      (sumrange_update_high ind)
      (sumrange_update_isum ind +
       (v - sumrange_update_get a i))`;

val sumrange_CumulativeTree_update_aux_complexityqtvc_statement =
  ``!(t : sumrange_update_tree)
      (a : int list)
      (i : int)
      (v : int)
      (c : int).
      sumrange_update_is_tree_for
        t a
        (sumrange_update_low (sumrange_update_indexes_of t))
        (sumrange_update_high (sumrange_update_indexes_of t)) /\
      sumrange_update_low (sumrange_update_indexes_of t) <= i /\
      i < sumrange_update_high (sumrange_update_indexes_of t)
      ==>
      case t of
        SumrangeUpdateLeaf ind =>
          let o1 =
            SumrangeUpdateLeaf
              (SumrangeUpdateIndexes
                (sumrange_update_low ind)
                (sumrange_update_high ind)
                v)
          in
            c + (1 : int) - c <= sumrange_update_depth t /\
            v - sumrange_update_isum ind =
              v - sumrange_update_get a i /\
            sumrange_update_low (sumrange_update_indexes_of o1) =
              sumrange_update_low (sumrange_update_indexes_of t) /\
            sumrange_update_high (sumrange_update_indexes_of o1) =
              sumrange_update_high (sumrange_update_indexes_of t) /\
            sumrange_update_is_tree_for
              o1 (sumrange_update_array a i v)
              (sumrange_update_low (sumrange_update_indexes_of o1))
              (sumrange_update_high (sumrange_update_indexes_of o1))
      | SumrangeUpdateNode ind l r =>
          if i <
             sumrange_update_high (sumrange_update_indexes_of l)
          then
            (sumrange_update_is_child t l /\
             sumrange_update_is_tree_for
               l a
               (sumrange_update_low (sumrange_update_indexes_of l))
               (sumrange_update_high (sumrange_update_indexes_of l)) /\
             sumrange_update_low (sumrange_update_indexes_of l) <= i /\
             i < sumrange_update_high (sumrange_update_indexes_of l)) /\
            (!(c1 : int) (l' : sumrange_update_tree).
              c1 - (c + (1 : int)) <= sumrange_update_depth l /\
              sumrange_update_low (sumrange_update_indexes_of l') =
                sumrange_update_low (sumrange_update_indexes_of l) /\
              sumrange_update_high (sumrange_update_indexes_of l') =
                sumrange_update_high (sumrange_update_indexes_of l) /\
              sumrange_update_is_tree_for
                l' (sumrange_update_array a i v)
                (sumrange_update_low (sumrange_update_indexes_of l'))
                (sumrange_update_high (sumrange_update_indexes_of l'))
              ==>
              let rebuilt =
                SumrangeUpdateNode
                  (sumrange_update_changed_indexes ind a i v)
                  l' r
              in
                c1 - c <= sumrange_update_depth t /\
                sumrange_update_low
                    (sumrange_update_indexes_of rebuilt) =
                  sumrange_update_low
                    (sumrange_update_indexes_of t) /\
                sumrange_update_high
                    (sumrange_update_indexes_of rebuilt) =
                  sumrange_update_high
                    (sumrange_update_indexes_of t) /\
                sumrange_update_is_tree_for
                  rebuilt (sumrange_update_array a i v)
                  (sumrange_update_low
                    (sumrange_update_indexes_of rebuilt))
                  (sumrange_update_high
                    (sumrange_update_indexes_of rebuilt)))
          else
            (sumrange_update_is_child t r /\
             sumrange_update_is_tree_for
               r a
               (sumrange_update_low (sumrange_update_indexes_of r))
               (sumrange_update_high (sumrange_update_indexes_of r)) /\
             sumrange_update_low (sumrange_update_indexes_of r) <= i /\
             i < sumrange_update_high (sumrange_update_indexes_of r)) /\
            (!(c1 : int) (r' : sumrange_update_tree).
              c1 - (c + (1 : int)) <= sumrange_update_depth r /\
              sumrange_update_low (sumrange_update_indexes_of r') =
                sumrange_update_low (sumrange_update_indexes_of r) /\
              sumrange_update_high (sumrange_update_indexes_of r') =
                sumrange_update_high (sumrange_update_indexes_of r) /\
              sumrange_update_is_tree_for
                r' (sumrange_update_array a i v)
                (sumrange_update_low (sumrange_update_indexes_of r'))
                (sumrange_update_high (sumrange_update_indexes_of r'))
              ==>
              let rebuilt =
                SumrangeUpdateNode
                  (sumrange_update_changed_indexes ind a i v)
                  l r'
              in
                c1 - c <= sumrange_update_depth t /\
                sumrange_update_low
                    (sumrange_update_indexes_of rebuilt) =
                  sumrange_update_low
                    (sumrange_update_indexes_of t) /\
                sumrange_update_high
                    (sumrange_update_indexes_of rebuilt) =
                  sumrange_update_high
                    (sumrange_update_indexes_of t) /\
                sumrange_update_is_tree_for
                  rebuilt (sumrange_update_array a i v)
                  (sumrange_update_low
                    (sumrange_update_indexes_of rebuilt))
                  (sumrange_update_high
                    (sumrange_update_indexes_of rebuilt)))``;
