(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_updateqtvc: the cumulative range-sum tree
  point-update verification condition, preserving the tree interval and
  establishing the updated-array cell, frame, and tree invariants.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  sumrange_ct_update_indexes =
    SumrangeCTUpdateIndexes int int int
End

val sumrange_ct_update_low_def = Define `
  sumrange_ct_update_low
    (SumrangeCTUpdateIndexes low high isum) = low`;

val sumrange_ct_update_high_def = Define `
  sumrange_ct_update_high
    (SumrangeCTUpdateIndexes low high isum) = high`;

val sumrange_ct_update_isum_def = Define `
  sumrange_ct_update_isum
    (SumrangeCTUpdateIndexes low high isum) = isum`;

Datatype:
  sumrange_ct_update_tree =
    SumrangeCTUpdateLeaf sumrange_ct_update_indexes
  | SumrangeCTUpdateNode
      sumrange_ct_update_indexes
      sumrange_ct_update_tree
      sumrange_ct_update_tree
End

val sumrange_ct_update_indexes_of_def = Define `
  (sumrange_ct_update_indexes_of
      (SumrangeCTUpdateLeaf ind) = ind) /\
  (sumrange_ct_update_indexes_of
      (SumrangeCTUpdateNode ind l r) = ind)`;

val sumrange_ct_update_to_num_def = Define `
  sumrange_ct_update_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sumrange_ct_update_get_def = Define `
  sumrange_ct_update_get (a : int list) (i : int) =
    if (0 : int) <= i /\
       sumrange_ct_update_to_num i < LENGTH a then
      EL (sumrange_ct_update_to_num i) a
    else
      (0 : int)`;

val sumrange_ct_update_array_def = Define `
  sumrange_ct_update_array
      (a : int list) (i : int) (v : int) =
    LUPDATE v (sumrange_ct_update_to_num i) a`;

val sumrange_ct_update_fun_update_def = Define `
  sumrange_ct_update_fun_update
      (f : int -> int) (i : int) (v : int) =
    \k. if k = i then v else f k`;

val sumrange_ct_update_sum_from_def = Define `
  (sumrange_ct_update_sum_from
      (a : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_ct_update_sum_from a start (SUC count) =
     EL start a +
     sumrange_ct_update_sum_from a (SUC start) count)`;

val sumrange_ct_update_sum_def = Define `
  sumrange_ct_update_sum
      (a : int list) (i : int) (j : int) =
    sumrange_ct_update_sum_from
      a
      (sumrange_ct_update_to_num i)
      (sumrange_ct_update_to_num (j - i))`;

val sumrange_ct_update_is_indexes_for_def = Define `
  sumrange_ct_update_is_indexes_for
      ind (a : int list) (i : int) (j : int) <=>
    sumrange_ct_update_low ind = i /\
    sumrange_ct_update_high ind = j /\
    (0 : int) <= i /\
    i < j /\
    j <= &(LENGTH a) /\
    sumrange_ct_update_isum ind =
      sumrange_ct_update_sum a i j`;

val sumrange_ct_update_is_tree_for_def = Define `
  (sumrange_ct_update_is_tree_for
      (SumrangeCTUpdateLeaf ind)
      (a : int list) (i : int) (j : int) <=>
     sumrange_ct_update_is_indexes_for ind a i j /\
     j = i + (1 : int)) /\
  (sumrange_ct_update_is_tree_for
      (SumrangeCTUpdateNode ind l r) a i j <=>
     sumrange_ct_update_is_indexes_for ind a i j /\
     i =
       sumrange_ct_update_low
         (sumrange_ct_update_indexes_of l) /\
     j =
       sumrange_ct_update_high
         (sumrange_ct_update_indexes_of r) /\
     (let m =
        sumrange_ct_update_high
          (sumrange_ct_update_indexes_of l)
      in
        m =
          sumrange_ct_update_low
            (sumrange_ct_update_indexes_of r) /\
        i < m /\
        m < j /\
        m = (i + j) quot (2 : int) /\
        sumrange_ct_update_is_tree_for l a i m /\
        sumrange_ct_update_is_tree_for r a m j))`;

val sumrange_CumulativeTree_updateqtvc_statement =
  ``!(i : int)
      (a : int list)
      (t : sumrange_ct_update_tree)
      (v : int).
      (0 : int) <= i /\
      i < &(LENGTH a) /\
      sumrange_ct_update_is_tree_for
        t a (0 : int) (&(LENGTH a))
      ==>
      sumrange_ct_update_is_tree_for
        t a
        (sumrange_ct_update_low
          (sumrange_ct_update_indexes_of t))
        (sumrange_ct_update_high
          (sumrange_ct_update_indexes_of t)) /\
      sumrange_ct_update_low
        (sumrange_ct_update_indexes_of t) <= i /\
      i <
        sumrange_ct_update_high
          (sumrange_ct_update_indexes_of t) /\
      !(t1 : sumrange_ct_update_tree).
        sumrange_ct_update_low
          (sumrange_ct_update_indexes_of t1) =
            sumrange_ct_update_low
              (sumrange_ct_update_indexes_of t) /\
        sumrange_ct_update_high
          (sumrange_ct_update_indexes_of t1) =
            sumrange_ct_update_high
              (sumrange_ct_update_indexes_of t) /\
        sumrange_ct_update_is_tree_for
          t1
          (sumrange_ct_update_array a i v)
          (sumrange_ct_update_low
            (sumrange_ct_update_indexes_of t1))
          (sumrange_ct_update_high
            (sumrange_ct_update_indexes_of t1))
        ==>
        ((0 : int) <= i /\ i < &(LENGTH a)) /\
        (LENGTH (sumrange_ct_update_array a i v) = LENGTH a
         ==>
         sumrange_ct_update_get
           (sumrange_ct_update_array a i v) =
           sumrange_ct_update_fun_update
             (sumrange_ct_update_get a) i v
         ==>
         sumrange_ct_update_get
           (sumrange_ct_update_array a i v) i = v /\
         (!k : int.
            (((0 : int) <= k /\
              k <
                &(LENGTH
                    (sumrange_ct_update_array a i v))) /\
             ~(k = i))
            ==>
            sumrange_ct_update_get
              (sumrange_ct_update_array a i v) k =
              sumrange_ct_update_get a k) /\
         sumrange_ct_update_is_tree_for
           t1
           (sumrange_ct_update_array a i v)
           (0 : int)
           (&(LENGTH
               (sumrange_ct_update_array a i v))))``;
