(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_updateqtvc: the verification condition for
  updating an integer cumulative-sum array, including point-update framing,
  loop-invariant preservation, and the final cumulative-array specification.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val sumrange_update_to_num_def = Define `
  sumrange_update_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val sumrange_update_get_def = Define `
  sumrange_update_get (xs : int list) (z : int) =
    if (0 : int) <= z /\
       sumrange_update_to_num z < LENGTH xs then
      EL (sumrange_update_to_num z) xs
    else
      (0 : int)`;

val sumrange_update_list_def = Define `
  sumrange_update_list
    (xs : int list) (z : int) (value : int) =
      if z < (0 : int) then xs
      else LUPDATE value (sumrange_update_to_num z) xs`;

val sumrange_update_fun_def = Define `
  sumrange_update_fun
    (f : int -> int) (z : int) (value : int) =
      \q. if q = z then value else f q`;

val sumrange_update_sum_from_def = Define `
  (sumrange_update_sum_from
      (xs : int list) (start : num) 0 = (0 : int)) /\
  (sumrange_update_sum_from xs start (SUC count) =
     (if start < LENGTH xs then EL start xs else (0 : int)) +
     sumrange_update_sum_from xs (SUC start) count)`;

val sumrange_update_sum_def = Define `
  sumrange_update_sum
    (xs : int list) (lower : int) (upper : int) =
      sumrange_update_sum_from
        xs
        (sumrange_update_to_num lower)
        (sumrange_update_to_num (upper - lower))`;

val sumrange_update_is_cumulative_def = Define `
  sumrange_update_is_cumulative
    (c : int list) (a : int list) <=>
      &(LENGTH c) = &(LENGTH a) + (1 : int) /\
      !k : int.
        (0 : int) <= k /\ k < &(LENGTH c) ==>
        sumrange_update_get c k =
          sumrange_update_sum a (0 : int) k`;

val sumrange_CumulativeArray_updateqtvc_statement =
  ``!(c : int list) (a : int list) (i : int) (v : int).
      sumrange_update_is_cumulative c a ==>
      (0 : int) <= i ==>
      i < &(LENGTH a) ==>
      (0 : int) <= i /\
      i < &(LENGTH c) /\
      (let o1 = i + (1 : int)
       in
         ((0 : int) <= o1 /\ o1 < &(LENGTH c)) /\
         (let incr =
            v - sumrange_update_get c o1 +
              sumrange_update_get c i
          in
            ((0 : int) <= i /\ i < &(LENGTH a)) /\
            (LENGTH (sumrange_update_list a i v) = LENGTH a ==>
             sumrange_update_get (sumrange_update_list a i v) =
               sumrange_update_fun (sumrange_update_get a) i v ==>
             (let o2 = &(LENGTH c) - (1 : int)
              in
              let o3 = i + (1 : int)
              in
                (o3 <= o2 + (1 : int) ==>
                 ((!k : int.
                     o3 <= k /\ k < &(LENGTH c) ==>
                     sumrange_update_get c k =
                       sumrange_update_sum
                         (sumrange_update_list a i v)
                         (0 : int) k -
                       incr) /\
                  (!k : int.
                     (0 : int) <= k /\ k < o3 ==>
                     sumrange_update_get c k =
                       sumrange_update_sum
                         (sumrange_update_list a i v)
                         (0 : int) k) /\
                  (!c1 : int list.
                     LENGTH c1 = LENGTH c ==>
                     ((!j : int.
                         ((o3 <= j /\ j <= o2) /\
                          (!k : int.
                             j <= k /\ k < &(LENGTH c1) ==>
                             sumrange_update_get c1 k =
                               sumrange_update_sum
                                 (sumrange_update_list a i v)
                                 (0 : int) k -
                               incr) /\
                          (!k : int.
                             (0 : int) <= k /\ k < j ==>
                             sumrange_update_get c1 k =
                               sumrange_update_sum
                                 (sumrange_update_list a i v)
                                 (0 : int) k)) ==>
                         ((0 : int) <= j /\ j < &(LENGTH c1)) /\
                         (let o4 =
                            sumrange_update_get c1 j + incr
                          in
                            ((0 : int) <= j /\
                             j < &(LENGTH c1)) /\
                            (LENGTH
                               (sumrange_update_list c1 j o4) =
                               LENGTH c1 ==>
                             sumrange_update_get
                               (sumrange_update_list c1 j o4) =
                               sumrange_update_fun
                                 (sumrange_update_get c1) j o4 ==>
                             (!k : int.
                                j + (1 : int) <= k /\
                                k <
                                  &(LENGTH
                                      (sumrange_update_list
                                         c1 j o4)) ==>
                                sumrange_update_get
                                  (sumrange_update_list c1 j o4) k =
                                  sumrange_update_sum
                                    (sumrange_update_list a i v)
                                    (0 : int) k -
                                  incr) /\
                             (!k : int.
                                (0 : int) <= k /\
                                k < j + (1 : int) ==>
                                sumrange_update_get
                                  (sumrange_update_list c1 j o4) k =
                                  sumrange_update_sum
                                    (sumrange_update_list a i v)
                                    (0 : int) k))))) /\
                      (((!k : int.
                           o2 + (1 : int) <= k /\
                           k < &(LENGTH c1) ==>
                           sumrange_update_get c1 k =
                             sumrange_update_sum
                               (sumrange_update_list a i v)
                               (0 : int) k -
                             incr) /\
                        (!k : int.
                           (0 : int) <= k /\
                           k < o2 + (1 : int) ==>
                           sumrange_update_get c1 k =
                             sumrange_update_sum
                               (sumrange_update_list a i v)
                               (0 : int) k)) ==>
                       sumrange_update_is_cumulative
                         c1 (sumrange_update_list a i v) /\
                       sumrange_update_get
                         (sumrange_update_list a i v) i = v /\
                       (!k : int.
                          (((0 : int) <= k /\
                            k <
                              &(LENGTH
                                  (sumrange_update_list a i v))) /\
                           ~(k = i)) ==>
                          sumrange_update_get
                            (sumrange_update_list a i v) k =
                            sumrange_update_get a k))))) /\
                (o2 + (1 : int) < o3 ==>
                 sumrange_update_is_cumulative
                   c (sumrange_update_list a i v) /\
                 sumrange_update_get
                   (sumrange_update_list a i v) i = v /\
                 (!k : int.
                    (((0 : int) <= k /\
                      k <
                        &(LENGTH (sumrange_update_list a i v))) /\
                     ~(k = i)) ==>
                    sumrange_update_get
                      (sumrange_update_list a i v) k =
                      sumrange_update_get a k))))))``;
