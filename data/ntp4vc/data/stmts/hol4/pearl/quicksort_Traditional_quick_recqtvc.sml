(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Traditional_quick_recqtvc: the traditional two-pointer
  quicksort verification condition, including scan invariants, swaps,
  recursive sorted subranges, and subarray permutations.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val quicksort_Traditional_quick_rec_vc =
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
        if r <= l + 1 then
          vc_sorted_sub a l r /\
          vc_permut_sub_prime
            a a (vc_to_nat l) (vc_to_nat r)
        else
          (0 <= l /\ l < &(LENGTH a)) /\
          (let v = vc_get a l in
           let vc_finish =
             \a1 : int list. \j1 : int.
               ((0 <= l /\ l < &(LENGTH a1)) /\
                0 <= j1 /\ j1 < &(LENGTH a1)) /\
               (!a2 : int list.
                  LENGTH a2 = LENGTH a1 ==>
                  vc_exchange a1 a2 l j1 ==>
                  ((0 <= r - l /\ j1 - l < r - l) /\
                   0 <= l /\ l <= j1 /\ j1 <= &(LENGTH a2)) /\
                  (!a3 : int list.
                     LENGTH a3 = LENGTH a2 ==>
                     vc_sorted_sub a3 l j1 /\
                     vc_permut_sub_prime
                       a2 a3 (vc_to_nat l) (vc_to_nat j1) ==>
                     (let o1 = j1 + 1 in
                        ((0 <= r - l /\ r - o1 < r - l) /\
                         0 <= o1 /\ o1 <= r /\
                         r <= &(LENGTH a3)) /\
                        (!a4 : int list.
                           LENGTH a4 = LENGTH a3 ==>
                           vc_sorted_sub a4 o1 r /\
                           vc_permut_sub_prime
                             a3 a4 (vc_to_nat o1) (vc_to_nat r) ==>
                           vc_sorted_sub a4 l r /\
                           vc_permut_sub_prime
                             a a4 (vc_to_nat l) (vc_to_nat r)))))
           in
           let vc_continue =
             \a1 : int list.
             \i : int. \i1 : int. \j : int. \j1 : int.
               ((0 <= i1 /\ i1 < &(LENGTH a1)) /\
                0 <= j1 /\ j1 < &(LENGTH a1)) /\
               (!a2 : int list.
                  LENGTH a2 = LENGTH a1 ==>
                  vc_exchange a1 a2 i1 j1 ==>
                  (0 <= j - i /\ j1 - i1 < j - i) /\
                  (l <= i1 /\ i1 < r - 1) /\
                  (!k : int.
                     l <= k /\ k <= i1 ==>
                     vc_get a2 k <= v) /\
                  (l < j1 /\ j1 <= r) /\
                  (!k : int.
                     j1 <= k /\ k < r ==>
                     v <= vc_get a2 k) /\
                  vc_permut_sub_prime
                    a a2 (vc_to_nat l) (vc_to_nat r) /\
                  vc_get a2 l = v)
           in
           let vc_decrement =
             \a1 : int list. \j : int. \j1 : int.
               (0 <= j1 /\ j1 - 1 < j1) /\
               (l <= j1 - 1 /\ j1 - 1 < j) /\
               (!k : int.
                  j1 - 1 < k /\ k < r ==>
                  v <= vc_get a1 k)
           in
           let vc_after_right =
             \a1 : int list.
             \i : int. \i1 : int. \j : int. \j1 : int.
               if v < vc_get a1 j1 then
                 if j1 = l then
                   if j1 <= i1 then
                     vc_finish a1 j1
                   else
                     vc_continue a1 i i1 j j1
                 else
                   vc_decrement a1 j j1
               else if j1 <= i1 then
                 vc_finish a1 j1
               else
                 vc_continue a1 i i1 j j1
           in
           let vc_right_scan =
             \a1 : int list. \i : int. \i1 : int. \j : int.
               ((l <= j - 1 /\ j - 1 < j) /\
                (!k : int.
                   j - 1 < k /\ k < r ==>
                   v <= vc_get a1 k)) /\
               (!j1 : int.
                  (l <= j1 /\ j1 < j) /\
                  (!k : int.
                     j1 < k /\ k < r ==>
                     v <= vc_get a1 k) ==>
                  (0 <= j1 /\ j1 < &(LENGTH a1)) /\
                  vc_after_right a1 i i1 j j1)
           in
             ((l <= l /\ l < r - 1) /\
              (!k : int.
                 l <= k /\ k <= l ==>
                 vc_get a k <= v) /\
              (l < r /\ r <= r) /\
              (!k : int.
                 r <= k /\ k < r ==>
                 v <= vc_get a k) /\
              vc_permut_sub_prime
                a a (vc_to_nat l) (vc_to_nat r) /\
              vc_get a l = v) /\
             (!j i : int.
              !a1 : int list.
                LENGTH a1 = LENGTH a ==>
                (l <= i /\ i < r - 1) /\
                (!k : int.
                   l <= k /\ k <= i ==>
                   vc_get a1 k <= v) /\
                (l < j /\ j <= r) /\
                (!k : int.
                   j <= k /\ k < r ==>
                   v <= vc_get a1 k) /\
                vc_permut_sub_prime
                  a a1 (vc_to_nat l) (vc_to_nat r) /\
                vc_get a1 l = v ==>
                ((i < i + 1 /\ i + 1 < r) /\
                 (!k : int.
                    l <= k /\ k < i + 1 ==>
                    vc_get a1 k <= v)) /\
                (!i1 : int.
                   (i < i1 /\ i1 < r) /\
                   (!k : int.
                      l <= k /\ k < i1 ==>
                      vc_get a1 k <= v) ==>
                   (0 <= i1 /\ i1 < &(LENGTH a1)) /\
                   (if vc_get a1 i1 < v then
                      if i1 = r - 1 then
                        vc_right_scan a1 i i1 j
                      else
                        (0 <= r - i1 /\
                         r - (i1 + 1) < r - i1) /\
                        (i < i1 + 1 /\ i1 + 1 < r) /\
                        (!k : int.
                           l <= k /\ k < i1 + 1 ==>
                           vc_get a1 k <= v)
                    else
                      vc_right_scan a1 i i1 j))))``;
