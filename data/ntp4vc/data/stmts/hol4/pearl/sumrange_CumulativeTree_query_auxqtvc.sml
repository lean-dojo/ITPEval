(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_query_auxqtvc: the cumulative-tree range-sum
  auxiliary verification condition, preserving recursive-call obligations
  and the final half-open integer range-sum relation. This file contains no
  proof.
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

val sumrange_query_is_child_def = Define `
  (sumrange_query_is_child (SumrangeQueryLeaf ind) child <=> F) /\
  (sumrange_query_is_child (SumrangeQueryNode ind l r) child <=>
     l = child \/ r = child)`;

val sumrange_query_call_context_def = Define `
  sumrange_query_call_context
      (parent : sumrange_query_tree)
      (child : sumrange_query_tree)
      (a : int list)
      (i : int)
      (j : int) <=>
    sumrange_query_is_child parent child /\
    sumrange_query_is_tree_for
      child a
      (sumrange_query_low (sumrange_query_indexes_of child))
      (sumrange_query_high (sumrange_query_indexes_of child)) /\
    (0 : int) <=
      sumrange_query_low (sumrange_query_indexes_of child) /\
    sumrange_query_low (sumrange_query_indexes_of child) <= i /\
    i < j /\
    j <= sumrange_query_high (sumrange_query_indexes_of child) /\
    sumrange_query_high (sumrange_query_indexes_of child) <=
      &(LENGTH a)`;

val sumrange_CumulativeTree_query_auxqtvc_statement =
  ``!(t : sumrange_query_tree)
      (a : int list)
      (i : int)
      (j : int).
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
      ((case t of
          SumrangeQueryLeaf ind => T
        | SumrangeQueryNode ind l r =>
            !o1 : bool.
              (if i = sumrange_query_low ind
               then
                 o1 =
                   (if j = sumrange_query_high ind then T else F)
               else o1 = F)
              ==>
              ~(o1 = T)
              ==>
              let m =
                sumrange_query_high (sumrange_query_indexes_of l)
              in
                if j <= m then
                  sumrange_query_call_context t l a i j
                else if m <= i then
                  sumrange_query_call_context t r a i j
                else
                  sumrange_query_call_context t r a m j /\
                  sumrange_query_call_context t l a i m) /\
       (!result : int.
          (case t of
             SumrangeQueryLeaf ind =>
               result = sumrange_query_isum ind
           | SumrangeQueryNode ind l r =>
               ?o1 : bool.
                 (if i = sumrange_query_low ind
                  then
                    o1 =
                      (if j = sumrange_query_high ind then T else F)
                  else o1 = F) /\
                 (if o1 = T then
                    result = sumrange_query_isum ind
                  else
                    let m =
                      sumrange_query_high (sumrange_query_indexes_of l)
                    in
                      if j <= m then
                        result = sumrange_query_sum a i j
                      else if m <= i then
                        result = sumrange_query_sum a i j
                      else
                        result =
                          sumrange_query_sum a i m +
                          sumrange_query_sum a m j))
          ==>
          result = sumrange_query_sum a i j))``;
