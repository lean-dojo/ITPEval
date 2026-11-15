(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_transposition_sort_Challenge3_odd_even_transposition_sortqtvc:
  the verification condition for odd-even transposition sort on an integer
  array, including permutation, parity-indexed ordering invariants, adjacent
  exchanges, inversion-count variants, and final sortedness. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pairTheory pred_setTheory sortingTheory;

val verifythis_2017_odd_even_transposition_sort_Challenge3_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_sorted =
      \xs : int list.
        !i1 i2 : int.
          0 <= i1 /\ i1 <= i2 /\ i2 < &(LENGTH xs) ==>
          vc_get xs i1 <= vc_get xs i2
    in
    let vc_odd_sorted =
      \xs : int list. \n : int.
        !i : int.
          0 <= i ==>
          2 * i + 2 < n ==>
          vc_get xs (2 * i + 1) <= vc_get xs (2 * i + 2)
    in
    let vc_even_sorted =
      \xs : int list. \n : int.
        !i : int.
          0 <= i ==>
          2 * i + 1 < n ==>
          vc_get xs (2 * i) <= vc_get xs (2 * i + 1)
    in
    let vc_exchange =
      \before : int list. \after : int list. \i : int. \j : int.
        after =
          LUPDATE (vc_get before i) (vc_to_num j)
            (LUPDATE (vc_get before j) (vc_to_num i) before)
    in
    let vc_inversions =
      \xs : int list.
        &(CARD
            {ij : int # int |
              0 <= FST ij /\
              FST ij < SND ij /\
              SND ij < &(LENGTH xs) /\
              vc_get xs (SND ij) < vc_get xs (FST ij)})
    in
      !a : int list.
        PERM a a /\
        !is_sorted : bool. !a1 : int list.
          LENGTH a1 = LENGTH a ==>
          PERM a a1 /\ (is_sorted ==> vc_sorted a1) ==>
          if ~is_sorted then
            (((0 : int) <= 0 /\
              (0 : int) <= 1 /\
              (1 : int) = 2 * 0 + 1) /\
             PERM a a1 /\
             vc_odd_sorted a1 1 /\
             (~T ==> vc_inversions a1 < vc_inversions a1)) /\
            (!half_i : int.
             !is_sorted1 : bool.
             !a2 : int list.
               LENGTH a2 = LENGTH a1 ==>
               (((0 : int) <= half_i /\
                 (0 : int) <= 2 * half_i + 1) /\
                PERM a a2 /\
                vc_odd_sorted a2 (2 * half_i + 1) /\
                (if is_sorted1 then
                   vc_inversions a2 = vc_inversions a1
                 else
                   vc_inversions a2 < vc_inversions a1)) ==>
               if 2 * half_i + 1 < &(LENGTH a2) - 1 then
                 let o1 = 2 * half_i + 1 + 1 in
                   ((0 : int) <= o1 /\ o1 < &(LENGTH a2)) /\
                   ((0 : int) <= 2 * half_i + 1 /\
                    2 * half_i + 1 < &(LENGTH a2)) /\
                   if vc_get a2 o1 < vc_get a2 (2 * half_i + 1) then
                     let o2 = 2 * half_i + 1 + 1 in
                       (((0 : int) <= 2 * half_i + 1 /\
                         2 * half_i + 1 < &(LENGTH a2)) /\
                        (0 : int) <= o2 /\
                        o2 < &(LENGTH a2)) /\
                       (!a3 : int list.
                          LENGTH a3 = LENGTH a2 ==>
                          vc_exchange a2 a3 (2 * half_i + 1) o2 ==>
                          ((0 : int) <=
                             &(LENGTH a2) - (2 * half_i + 1) /\
                           &(LENGTH a3) - (2 * half_i + 1 + 2) <
                             &(LENGTH a2) - (2 * half_i + 1)) /\
                          ((0 : int) <= half_i + 1 /\
                           (0 : int) <= 2 * half_i + 1 + 2 /\
                           2 * half_i + 1 + 2 =
                             2 * (half_i + 1) + 1) /\
                          PERM a a3 /\
                          vc_odd_sorted a3 (2 * half_i + 1 + 2) /\
                          (if F = T then
                             vc_inversions a3 = vc_inversions a1
                           else
                             vc_inversions a3 < vc_inversions a1))
                   else
                     ((0 : int) <=
                        &(LENGTH a2) - (2 * half_i + 1) /\
                      &(LENGTH a2) - (2 * half_i + 1 + 2) <
                        &(LENGTH a2) - (2 * half_i + 1)) /\
                     ((0 : int) <= half_i + 1 /\
                      (0 : int) <= 2 * half_i + 1 + 2 /\
                      2 * half_i + 1 + 2 =
                        2 * (half_i + 1) + 1) /\
                     PERM a a2 /\
                     vc_odd_sorted a2 (2 * half_i + 1 + 2) /\
                     (if is_sorted1 then
                        vc_inversions a2 = vc_inversions a1
                      else
                        vc_inversions a2 < vc_inversions a1)
               else
                 (((0 : int) <= 0 /\
                   (0 : int) <= 0 /\
                   (0 : int) = 2 * 0) /\
                  (0 : int) <= 0 /\
                  PERM a a2 /\
                  (is_sorted1 ==>
                    vc_odd_sorted a2 (&(LENGTH a2))) /\
                  vc_even_sorted a2 0 /\
                  (if is_sorted1 then
                     vc_inversions a2 = vc_inversions a1
                   else
                     vc_inversions a2 < vc_inversions a1) /\
                  (is_sorted1 \/
                   vc_inversions a2 < vc_inversions a1)) /\
                 (!half_i1 : int.
                  !is_sorted2 : bool.
                  !a3 : int list.
                    LENGTH a3 = LENGTH a2 ==>
                    (((0 : int) <= half_i1 /\
                      (0 : int) <= 2 * half_i1) /\
                     (0 : int) <= 2 * half_i1 /\
                     PERM a a3 /\
                     (is_sorted2 ==>
                       vc_odd_sorted a3 (&(LENGTH a3))) /\
                     vc_even_sorted a3 (2 * half_i1) /\
                     (if is_sorted2 then
                        vc_inversions a3 = vc_inversions a1
                      else
                        vc_inversions a3 < vc_inversions a1) /\
                     (is_sorted2 \/
                      vc_inversions a3 < vc_inversions a1)) ==>
                    if 2 * half_i1 < &(LENGTH a3) - 1 then
                      let o1 = 2 * half_i1 + 1 in
                        ((0 : int) <= o1 /\ o1 < &(LENGTH a3)) /\
                        ((0 : int) <= 2 * half_i1 /\
                         2 * half_i1 < &(LENGTH a3)) /\
                        if vc_get a3 o1 < vc_get a3 (2 * half_i1)
                        then
                          let o2 = 2 * half_i1 + 1 in
                            (((0 : int) <= 2 * half_i1 /\
                              2 * half_i1 < &(LENGTH a3)) /\
                             (0 : int) <= o2 /\
                             o2 < &(LENGTH a3)) /\
                            (!a4 : int list.
                               LENGTH a4 = LENGTH a3 ==>
                               vc_exchange a3 a4 (2 * half_i1) o2 ==>
                               ((0 : int) <=
                                  &(LENGTH a3) - 2 * half_i1 /\
                                &(LENGTH a4) - (2 * half_i1 + 2) <
                                  &(LENGTH a3) - 2 * half_i1) /\
                               ((0 : int) <= half_i1 + 1 /\
                                (0 : int) <= 2 * half_i1 + 2 /\
                                2 * half_i1 + 2 =
                                  2 * (half_i1 + 1)) /\
                               (0 : int) <= 2 * half_i1 + 2 /\
                               PERM a a4 /\
                               (F = T ==>
                                 vc_odd_sorted a4 (&(LENGTH a4))) /\
                               vc_even_sorted a4 (2 * half_i1 + 2) /\
                               (if F = T then
                                  vc_inversions a4 = vc_inversions a1
                                else
                                  vc_inversions a4 <
                                    vc_inversions a1) /\
                               (F = T \/
                                vc_inversions a4 < vc_inversions a1))
                        else
                          ((0 : int) <=
                             &(LENGTH a3) - 2 * half_i1 /\
                           &(LENGTH a3) - (2 * half_i1 + 2) <
                             &(LENGTH a3) - 2 * half_i1) /\
                          ((0 : int) <= half_i1 + 1 /\
                           (0 : int) <= 2 * half_i1 + 2 /\
                           2 * half_i1 + 2 =
                             2 * (half_i1 + 1)) /\
                          (0 : int) <= 2 * half_i1 + 2 /\
                          PERM a a3 /\
                          (is_sorted2 ==>
                            vc_odd_sorted a3 (&(LENGTH a3))) /\
                          vc_even_sorted a3 (2 * half_i1 + 2) /\
                          (if is_sorted2 then
                             vc_inversions a3 = vc_inversions a1
                           else
                             vc_inversions a3 < vc_inversions a1) /\
                          (is_sorted2 \/
                           vc_inversions a3 < vc_inversions a1)
                    else
                      ((((0 : int) <=
                           (if is_sorted then 0 else 1) /\
                         (if is_sorted2 then 0 else 1) <
                           (if is_sorted then 0 else 1)) \/
                        ((if is_sorted then 0 else 1) =
                           (if is_sorted2 then 0 else 1) /\
                         (0 : int) <= vc_inversions a1 /\
                         vc_inversions a3 < vc_inversions a1)) /\
                       PERM a a3 /\
                       (is_sorted2 ==> vc_sorted a3))))
          else
            vc_sorted a1 /\ PERM a a1``;
