(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_queryqtvc: the cumulative-sum array query
  verification condition, asserting index bounds and that the difference of
  two cumulative entries equals the sum over the corresponding half-open
  range. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val sumrange_query_to_num_def = Define `
  sumrange_query_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val sumrange_query_get_def = Define `
  sumrange_query_get (xs : int list) (z : int) =
    if sumrange_query_to_num z < LENGTH xs then
      EL (sumrange_query_to_num z) xs
    else
      (0 : int)`;

val sumrange_query_sum_from_def = Define `
  (sumrange_query_sum_from
      (xs : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_query_sum_from xs start (SUC count) =
     (if start < LENGTH xs then EL start xs else (0 : int)) +
     sumrange_query_sum_from xs (SUC start) count)`;

val sumrange_query_sum_def = Define `
  sumrange_query_sum
    (xs : int list) (lower : int) (upper : int) =
      sumrange_query_sum_from
        xs
        (sumrange_query_to_num lower)
        (sumrange_query_to_num (upper - lower))`;

val sumrange_query_is_cumulative_def = Define `
  sumrange_query_is_cumulative
    (c : int list) (a : int list) <=>
      &(LENGTH c) = &(LENGTH a) + (1 : int) /\
      !k : int.
        (0 : int) <= k /\ k < &(LENGTH c) ==>
        sumrange_query_get c k =
          sumrange_query_sum a (0 : int) k`;

val sumrange_CumulativeArray_queryqtvc_statement =
  ``!(c : int list) (a : int list) (i : int) (j : int).
      sumrange_query_is_cumulative c a /\
      (0 : int) <= i /\
      i <= j /\
      j < &(LENGTH c)
      ==>
      (0 : int) <= i /\
      i < &(LENGTH c) /\
      (0 : int) <= j /\
      j < &(LENGTH c) /\
      sumrange_query_get c j - sumrange_query_get c i =
        sumrange_query_sum a i j``;
