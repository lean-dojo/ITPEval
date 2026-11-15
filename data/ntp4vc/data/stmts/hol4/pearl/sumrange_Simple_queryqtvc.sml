(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_Simple_queryqtvc: the simple linear range-sum query
  verification condition, including loop initialization, preservation, and
  exit obligations for a half-open interval. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val sumrange_simple_to_num_def = Define `
  sumrange_simple_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sumrange_simple_get_def = Define `
  sumrange_simple_get (a : int list) (i : int) =
    if sumrange_simple_to_num i < LENGTH a then
      EL (sumrange_simple_to_num i) a
    else
      (0 : int)`;

val sumrange_simple_sum_from_def = Define `
  (sumrange_simple_sum_from
      (a : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_simple_sum_from a start (SUC count) =
     (if start < LENGTH a then EL start a else (0 : int)) +
     sumrange_simple_sum_from a (SUC start) count)`;

val sumrange_simple_sum_def = Define `
  sumrange_simple_sum
      (a : int list) (i : int) (j : int) =
    sumrange_simple_sum_from
      a
      (sumrange_simple_to_num i)
      (sumrange_simple_to_num (j - i))`;

val sumrange_Simple_queryqtvc_statement =
  ``!(i : int) (j : int) (a : int list).
      (0 : int) <= i /\
      i <= j /\
      j <= &(LENGTH a)
      ==>
      let o1 = j - (1 : int)
      in
        (i <= o1 + (1 : int) ==>
         (0 : int) = sumrange_simple_sum a i i /\
         !s : int.
           (!k : int.
              ((i <= k /\ k <= o1) /\
               s = sumrange_simple_sum a i k)
              ==>
              ((0 : int) <= k /\ k < &(LENGTH a)) /\
              s + sumrange_simple_get a k =
                sumrange_simple_sum a i (k + (1 : int))) /\
           (s = sumrange_simple_sum a i (o1 + (1 : int))
            ==>
            s = sumrange_simple_sum a i j)) /\
        (o1 + (1 : int) < i ==>
         (0 : int) = sumrange_simple_sum a i j)``;
