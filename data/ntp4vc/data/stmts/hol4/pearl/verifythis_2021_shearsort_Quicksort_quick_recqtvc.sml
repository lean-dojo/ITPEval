(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_Quicksort_quick_recqtvc: the recursive
  Bentley-style quicksort verification condition, including partition-loop
  invariants, swaps, recursively sorted subranges, and subarray permutations.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val verifythis_2021_shearsort_Quicksort_quick_rec_vc =
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
           let o1 = r - 1 in
           let o2 = l + 1 in
             (o2 <= o1 + 1 ==>
              ((vc_get a l = v /\ l <= l /\ l < o2) /\
               (!j : int.
                  l < j /\ j <= l ==>
                  vc_get a j < v) /\
               (!j : int.
                  l < j /\ j < o2 ==>
                  v <= vc_get a j) /\
               vc_permut_sub_prime
                 a a (vc_to_nat l) (vc_to_nat r)) /\
              (!m : int.
               !a1 : int list.
                 LENGTH a1 = LENGTH a ==>
                 (!i : int.
                    (o2 <= i /\ i <= o1) /\
                    (vc_get a1 l = v /\ l <= m /\ m < i) /\
                    (!j : int.
                       l < j /\ j <= m ==>
                       vc_get a1 j < v) /\
                    (!j : int.
                       m < j /\ j < i ==>
                       v <= vc_get a1 j) /\
                    vc_permut_sub_prime
                      a a1 (vc_to_nat l) (vc_to_nat r) ==>
                    (0 <= i /\ i < &(LENGTH a1)) /\
                    (if vc_get a1 i < v then
                       ((0 <= i /\ i < &(LENGTH a1)) /\
                        0 <= m + 1 /\
                        m + 1 < &(LENGTH a1)) /\
                       (!a2 : int list.
                          LENGTH a2 = LENGTH a1 ==>
                          vc_exchange a1 a2 i (m + 1) ==>
                          (vc_get a2 l = v /\
                           l <= m + 1 /\
                           m + 1 < i + 1) /\
                          (!j : int.
                             l < j /\ j <= m + 1 ==>
                             vc_get a2 j < v) /\
                          (!j : int.
                             m + 1 < j /\ j < i + 1 ==>
                             v <= vc_get a2 j) /\
                          vc_permut_sub_prime
                            a a2 (vc_to_nat l) (vc_to_nat r))
                     else
                       (vc_get a1 l = v /\
                        l <= m /\
                        m < i + 1) /\
                       (!j : int.
                          l < j /\ j <= m ==>
                          vc_get a1 j < v) /\
                       (!j : int.
                          m < j /\ j < i + 1 ==>
                          v <= vc_get a1 j) /\
                       vc_permut_sub_prime
                         a a1 (vc_to_nat l) (vc_to_nat r))) /\
                 ((vc_get a1 l = v /\
                   l <= m /\
                   m < o1 + 1) /\
                  (!j : int.
                     l < j /\ j <= m ==>
                     vc_get a1 j < v) /\
                  (!j : int.
                     m < j /\ j < o1 + 1 ==>
                     v <= vc_get a1 j) /\
                  vc_permut_sub_prime
                    a a1 (vc_to_nat l) (vc_to_nat r) ==>
                  ((0 <= l /\ l < &(LENGTH a1)) /\
                   0 <= m /\ m < &(LENGTH a1)) /\
                  (!a2 : int list.
                     LENGTH a2 = LENGTH a1 ==>
                     vc_exchange a1 a2 l m ==>
                     ((0 <= r - l /\ m - l < r - l) /\
                      0 <= l /\
                      l <= m /\
                      m <= &(LENGTH a2)) /\
                     (!a3 : int list.
                        LENGTH a3 = LENGTH a2 ==>
                        vc_sorted_sub a3 l m /\
                        vc_permut_sub_prime
                          a2 a3 (vc_to_nat l) (vc_to_nat m) ==>
                        (let o3 = m + 1 in
                           ((0 <= r - l /\ r - o3 < r - l) /\
                            0 <= o3 /\
                            o3 <= r /\
                            r <= &(LENGTH a3)) /\
                           (!a4 : int list.
                              LENGTH a4 = LENGTH a3 ==>
                              vc_sorted_sub a4 o3 r /\
                              vc_permut_sub_prime
                                a3 a4
                                (vc_to_nat o3)
                                (vc_to_nat r) ==>
                              vc_sorted_sub a4 l r /\
                              vc_permut_sub_prime
                                a a4
                                (vc_to_nat l)
                                (vc_to_nat r)))))))) /\
             (o1 + 1 < o2 ==>
              (0 <= l /\ l < &(LENGTH a)) /\
              (!a1 : int list.
                 LENGTH a1 = LENGTH a ==>
                 vc_exchange a a1 l l ==>
                 ((0 <= r - l /\ l - l < r - l) /\
                  0 <= l /\
                  l <= l /\
                  l <= &(LENGTH a1)) /\
                 (!a2 : int list.
                    LENGTH a2 = LENGTH a1 ==>
                    vc_sorted_sub a2 l l /\
                    vc_permut_sub_prime
                      a1 a2 (vc_to_nat l) (vc_to_nat l) ==>
                    (let o3 = l + 1 in
                       ((0 <= r - l /\ r - o3 < r - l) /\
                        0 <= o3 /\
                        o3 <= r /\
                        r <= &(LENGTH a2)) /\
                       (!a3 : int list.
                          LENGTH a3 = LENGTH a2 ==>
                          vc_sorted_sub a3 o3 r /\
                          vc_permut_sub_prime
                            a2 a3 (vc_to_nat o3) (vc_to_nat r) ==>
                          vc_sorted_sub a3 l r /\
                          vc_permut_sub_prime
                            a a3 (vc_to_nat l) (vc_to_nat r)))))))
        else
          vc_sorted_sub a l r /\
          vc_permut_sub_prime
            a a (vc_to_nat l) (vc_to_nat r)``;
