(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc: a
  bottom-up mergesort verification condition over lists ordered by a total
  preorder, preserving permutation and sorted-run loop invariants. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val mergesort_array_BottomUpMergesort_bottom_up_mergesort_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : 'a list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else ARB
    in
    let vc_min =
      \x y : int. if x <= y then x else y
    in
    let vc_slice =
      \xs : 'a list. \lower upper : num.
        TAKE (upper - lower) (DROP lower xs)
    in
    let vc_permut_sub =
      \xs ys : 'a list. \lower upper : num.
        LENGTH xs = LENGTH ys /\
        0 <= lower /\ lower <= LENGTH xs /\
        0 <= upper /\ upper <= LENGTH xs /\
        PERM
          (vc_slice xs lower upper)
          (vc_slice ys lower upper)
    in
    let vc_sorted_sub =
      \ord : 'a -> 'a -> bool.
      \xs : 'a list.
      \lower upper : int.
        !i1 i2 : int.
          lower <= i1 /\ i1 < i2 /\ i2 < upper ==>
          ord (vc_get xs i1) (vc_get xs i2)
    in
    let vc_sorted =
      \ord : 'a -> 'a -> bool.
      \xs : 'a list.
        !i1 i2 : int.
          0 <= i1 /\ i1 < i2 /\ i2 < &(LENGTH xs) ==>
          ord (vc_get xs i1) (vc_get xs i2)
    in
      !ord : 'a -> 'a -> bool.
        ((!x : 'a. ord x x) /\
         (!x y z : 'a. ord x y /\ ord y z ==> ord x z) /\
         (!x y : 'a. ord x y \/ ord y x)) ==>
        !a : 'a list.
          let n = &(LENGTH a) in
            !tmp : 'a list.
              LENGTH tmp = LENGTH a /\
              (!i : int.
                 0 <= i /\ i < &(LENGTH tmp) ==>
                 vc_get tmp i = vc_get a i) ==>
              ((1 : int) <= 1 /\
               PERM a a /\
               (!k : int.
                  let l = k * (1 : int) in
                    0 <= l /\ l < n ==>
                    vc_sorted_sub
                      ord a l (vc_min n (l + 1)))) /\
              (!len : int.
               !tmp1 a1 : 'a list.
                 LENGTH tmp1 = LENGTH tmp ==>
                 LENGTH a1 = LENGTH a ==>
                 1 <= len /\
                 PERM a a1 /\
                 (!k : int.
                    let l = k * len in
                      0 <= l /\ l < n ==>
                      vc_sorted_sub
                        ord a1 l (vc_min n (l + len))) ==>
                 if len < n then
                   (((0 : int) <= 0 /\
                     (0 : int) = 2 * 0 * len) /\
                    PERM a1 a1 /\
                    (!k : int.
                       let l = k * len in
                         0 <= l /\ l < n ==>
                         vc_sorted_sub
                           ord a1 l (vc_min n (l + len))) /\
                    (!k : int.
                       let l = k * (2 * len) in
                         0 <= l /\ l < 0 ==>
                         vc_sorted_sub
                           ord a1 l (vc_min n (l + 2 * len)))) /\
                   (!i : int.
                    !tmp2 a2 : 'a list.
                      LENGTH tmp2 = LENGTH tmp1 ==>
                      LENGTH a2 = LENGTH a1 ==>
                      0 <= 2 * i * len /\
                      PERM a1 a2 /\
                      (!k : int.
                         let l = k * len in
                           2 * i * len <= l /\ l < n ==>
                           vc_sorted_sub
                             ord a2 l (vc_min n (l + len))) /\
                      (!k : int.
                         let l = k * (2 * len) in
                           0 <= l /\ l < 2 * i * len ==>
                           vc_sorted_sub
                             ord a2 l (vc_min n (l + 2 * len))) ==>
                      if 2 * i * len < n - len then
                        let mid = 2 * i * len + len in
                        let hi = vc_min n (mid + len) in
                          ((0 <= 2 * i * len /\
                            2 * i * len <= mid /\
                            mid <= hi /\
                            hi <= &(LENGTH tmp2) /\
                            LENGTH tmp2 = LENGTH a2) /\
                           vc_sorted_sub ord a2 (2 * i * len) mid /\
                           vc_sorted_sub ord a2 mid hi) /\
                          (!a3 : 'a list.
                             LENGTH a3 = LENGTH a2 ==>
                             vc_sorted_sub
                               ord a3 (2 * i * len) hi /\
                             vc_permut_sub
                               a2 a3
                               (vc_to_nat (2 * i * len))
                               (vc_to_nat hi) /\
                             (!i1 : int.
                                ((0 <= i1 /\ i1 < 2 * i * len) \/
                                 (hi <= i1 /\
                                  i1 < &(LENGTH a3))) ==>
                                vc_get a3 i1 = vc_get a2 i1) ==>
                             (0 <= n + len - 2 * i * len /\
                              n + len - (mid + len) <
                                n + len - 2 * i * len) /\
                             (0 <= mid + len /\
                              mid + len = 2 * (i + 1) * len) /\
                             PERM a1 a3 /\
                             (!k : int.
                                let l = k * len in
                                  mid + len <= l /\ l < n ==>
                                  vc_sorted_sub
                                    ord a3 l
                                      (vc_min n (l + len))) /\
                             (!k : int.
                                let l = k * (2 * len) in
                                  0 <= l /\ l < mid + len ==>
                                  vc_sorted_sub
                                    ord a3 l
                                      (vc_min n (l + 2 * len))))
                      else
                        (0 <= 2 * n - len /\
                         2 * n - 2 * len < 2 * n - len) /\
                        1 <= 2 * len /\
                        PERM a a2 /\
                        (!k : int.
                           let l = k * (2 * len) in
                             0 <= l /\ l < n ==>
                             vc_sorted_sub
                               ord a2 l
                                 (vc_min n (l + 2 * len))))
                 else
                   vc_sorted ord a1 /\ PERM a a1)``;
