(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_createqtvc: the cumulative-sum array
  creation verification condition, including zero initialization,
  loop-invariant preservation under array update, and the final
  cumulative-array specification. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val sumrange_create_to_num_def = Define `
  sumrange_create_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val sumrange_create_get_def = Define `
  sumrange_create_get (xs : int list) (z : int) =
    if sumrange_create_to_num z < LENGTH xs then
      EL (sumrange_create_to_num z) xs
    else
      (0 : int)`;

val sumrange_create_sum_from_def = Define `
  (sumrange_create_sum_from
      (xs : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_create_sum_from xs start (SUC count) =
     (if start < LENGTH xs then EL start xs else (0 : int)) +
     sumrange_create_sum_from xs (SUC start) count)`;

val sumrange_create_sum_def = Define `
  sumrange_create_sum
    (xs : int list) (lower : int) (upper : int) =
      sumrange_create_sum_from
        xs
        (sumrange_create_to_num lower)
        (sumrange_create_to_num (upper - lower))`;

val sumrange_create_prefix_def = Define `
  sumrange_create_prefix
    (s : int list) (a : int list) (upper : int) <=>
      !k : int.
        (0 : int) <= k /\ k < upper ==>
        sumrange_create_get s k =
          sumrange_create_sum a (0 : int) k`;

val sumrange_create_is_cumulative_def = Define `
  sumrange_create_is_cumulative
    (c : int list) (a : int list) <=>
      &(LENGTH c) = &(LENGTH a) + (1 : int) /\
      !i : int.
        (0 : int) <= i /\ i < &(LENGTH c) ==>
        sumrange_create_get c i =
          sumrange_create_sum a (0 : int) i`;

val sumrange_create_update_step_def = Define `
  sumrange_create_update_step
    (s1 : int list) (a : int list) (i : int) <=>
      let o2 = i - (1 : int)
      in
        ((0 : int) <= o2 /\ o2 < &(LENGTH a)) /\
        (let o3 = i - (1 : int)
         in
           ((0 : int) <= o3 /\ o3 < &(LENGTH s1)) /\
           (let o4 =
              sumrange_create_get s1 o3 +
              sumrange_create_get a o2
            in
              ((0 : int) <= i /\ i < &(LENGTH s1)) /\
              (LENGTH
                 (LUPDATE
                    o4
                    (sumrange_create_to_num i)
                    s1) =
                 LENGTH s1 ==>
               (\z : int.
                  sumrange_create_get
                    (LUPDATE
                       o4
                       (sumrange_create_to_num i)
                       s1)
                    z) =
                 (\z : int.
                    if z = i then o4
                    else sumrange_create_get s1 z) ==>
               sumrange_create_prefix
                 (LUPDATE
                    o4
                    (sumrange_create_to_num i)
                    s1)
                 a
                 (i + (1 : int)))))`;

val sumrange_CumulativeArray_createqtvc_statement =
  ``!a : int list.
      let l = &(LENGTH a)
      in
      let o1 = l + (1 : int)
      in
        (0 : int) <= o1 /\
        !s : int list.
          ((!i : int.
              (0 : int) <= i /\ i < o1 ==>
              sumrange_create_get s i = (0 : int)) /\
           &(LENGTH s) = o1) ==>
          (((1 : int) <= l + (1 : int) ==>
            sumrange_create_prefix s a (1 : int) /\
            !s1 : int list.
              LENGTH s1 = LENGTH s ==>
              ((!i : int.
                  (((1 : int) <= i /\ i <= l) /\
                   sumrange_create_prefix s1 a i) ==>
                  sumrange_create_update_step s1 a i) /\
               (sumrange_create_prefix
                  s1 a (l + (1 : int)) ==>
                sumrange_create_is_cumulative s1 a))) /\
           (l + (1 : int) < (1 : int) ==>
            sumrange_create_is_cumulative s a))``;
