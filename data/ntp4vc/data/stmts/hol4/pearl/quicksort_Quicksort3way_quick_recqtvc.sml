(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Quicksort3way_quick_recqtvc: the recursive three-way
  quicksort verification condition, including partition invariants, swaps,
  termination measures, recursive sortedness, and subarray permutation.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val quicksort_Quicksort3way_quick_rec_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : int list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else 0
    in
    let vc_slice =
      \xs : int list. \lower : num. \upper : num.
        TAKE (upper - lower) (DROP lower xs)
    in
    let vc_permut_sub_prime =
      \xs : int list. \ys : int list. \lower : num. \upper : num.
        LENGTH xs = LENGTH ys /\
        vc_slice xs 0 lower = vc_slice ys 0 lower /\
        vc_slice xs upper (LENGTH xs) =
          vc_slice ys upper (LENGTH xs) /\
        PERM (vc_slice xs lower upper) (vc_slice ys lower upper)
    in
    let vc_exchange =
      \before : int list. \after : int list. \i : int. \j : int.
        after =
          LUPDATE (vc_get before i) (vc_to_nat j)
            (LUPDATE (vc_get before j) (vc_to_nat i) before)
    in
    let vc_sorted_sub =
      \xs : int list. \lower : int. \upper : int.
        !p q : int.
          lower <= p /\ p <= q /\ q < upper ==>
          vc_get xs p <= vc_get xs q
    in
      !l r : int.
      !a : int list.
        0 <= l ==>
        l <= r ==>
        r <= &(LENGTH a) ==>
        if l + 1 < r then
          (0 <= l /\ l < &(LENGTH a)) /\
          (let v = vc_get a l in
           let o1 = l + 1 in
             (l <= l /\ l < o1 /\ o1 <= r /\ r <= r) /\
             (!j : int.
                l <= j /\ j < l ==>
                vc_get a j < v) /\
             (!j : int.
                l <= j /\ j < o1 ==>
                vc_get a j = v) /\
             (!j : int.
                r <= j /\ j < r ==>
                v < vc_get a j) /\
             vc_permut_sub_prime
               a a (vc_to_nat l) (vc_to_nat r)) /\
          (!i mr ml : int.
           !a1 : int list.
             LENGTH a1 = LENGTH a ==>
             (l <= ml /\ ml < i /\ i <= mr /\ mr <= r) /\
             (!j : int.
                l <= j /\ j < ml ==>
                vc_get a1 j < vc_get a l) /\
             (!j : int.
                ml <= j /\ j < i ==>
                vc_get a1 j = vc_get a l) /\
             (!j : int.
                mr <= j /\ j < r ==>
                vc_get a l < vc_get a1 j) /\
             vc_permut_sub_prime
               a a1 (vc_to_nat l) (vc_to_nat r) ==>
             if i < mr then
               (0 <= i /\ i < &(LENGTH a1)) /\
               (if vc_get a1 i < vc_get a l then
                  ((0 <= ml /\ ml < &(LENGTH a1)) /\
                   0 <= i /\ i < &(LENGTH a1)) /\
                  (!a2 : int list.
                     LENGTH a2 = LENGTH a1 ==>
                     vc_exchange a1 a2 ml i ==>
                     (0 <= mr - i /\
                      mr - (i + 1) < mr - i) /\
                     (l <= ml + 1 /\
                      ml + 1 < i + 1 /\
                      i + 1 <= mr /\
                      mr <= r) /\
                     (!j : int.
                        l <= j /\ j < ml + 1 ==>
                        vc_get a2 j < vc_get a l) /\
                     (!j : int.
                        ml + 1 <= j /\ j < i + 1 ==>
                        vc_get a2 j = vc_get a l) /\
                     (!j : int.
                        mr <= j /\ j < r ==>
                        vc_get a l < vc_get a2 j) /\
                     vc_permut_sub_prime
                       a a2 (vc_to_nat l) (vc_to_nat r))
                else
                  (0 <= i /\ i < &(LENGTH a1)) /\
                  (if vc_get a l < vc_get a1 i then
                     ((0 <= i /\ i < &(LENGTH a1)) /\
                      0 <= mr - 1 /\
                      mr - 1 < &(LENGTH a1)) /\
                     (!a2 : int list.
                        LENGTH a2 = LENGTH a1 ==>
                        vc_exchange a1 a2 i (mr - 1) ==>
                        (0 <= mr - i /\
                         mr - 1 - i < mr - i) /\
                        (l <= ml /\
                         ml < i /\
                         i <= mr - 1 /\
                         mr - 1 <= r) /\
                        (!j : int.
                           l <= j /\ j < ml ==>
                           vc_get a2 j < vc_get a l) /\
                        (!j : int.
                           ml <= j /\ j < i ==>
                           vc_get a2 j = vc_get a l) /\
                        (!j : int.
                           mr - 1 <= j /\ j < r ==>
                           vc_get a l < vc_get a2 j) /\
                        vc_permut_sub_prime
                          a a2 (vc_to_nat l) (vc_to_nat r))
                   else
                     (0 <= mr - i /\
                      mr - (i + 1) < mr - i) /\
                     (l <= ml /\
                      ml < i + 1 /\
                      i + 1 <= mr /\
                      mr <= r) /\
                     (!j : int.
                        l <= j /\ j < ml ==>
                        vc_get a1 j < vc_get a l) /\
                     (!j : int.
                        ml <= j /\ j < i + 1 ==>
                        vc_get a1 j = vc_get a l) /\
                     (!j : int.
                        mr <= j /\ j < r ==>
                        vc_get a l < vc_get a1 j) /\
                     vc_permut_sub_prime
                       a a1 (vc_to_nat l) (vc_to_nat r)))
             else
               ((0 <= r - l /\ ml - l < r - l) /\
                0 <= l /\
                l <= ml /\
                ml <= &(LENGTH a1)) /\
               (!a2 : int list.
                  LENGTH a2 = LENGTH a1 ==>
                  vc_sorted_sub a2 l ml /\
                  vc_permut_sub_prime
                    a1 a2 (vc_to_nat l) (vc_to_nat ml) ==>
                  ((0 <= r - l /\ r - mr < r - l) /\
                   0 <= mr /\
                   mr <= r /\
                   r <= &(LENGTH a2)) /\
                  (!a3 : int list.
                     LENGTH a3 = LENGTH a2 ==>
                     vc_sorted_sub a3 mr r /\
                     vc_permut_sub_prime
                       a2 a3 (vc_to_nat mr) (vc_to_nat r) ==>
                     vc_sorted_sub a3 l r /\
                     vc_permut_sub_prime
                       a a3 (vc_to_nat l) (vc_to_nat r))))
        else
          vc_sorted_sub a l r /\
          vc_permut_sub_prime
            a a (vc_to_nat l) (vc_to_nat r)``;
