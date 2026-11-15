(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_natural_mergesortqtvc: the natural
  mergesort verification condition over lists ordered by a total preorder,
  preserving sorted runs, permutation, and loop-variant obligations. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val mergesort_array_NaturalMergesort_natural_mergesort_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : 'a list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else ARB
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
          let n = &(LENGTH a)
          in
            if n <= (1 : int) then
              vc_sorted ord a /\ PERM a a
            else
              !tmp : 'a list.
                LENGTH tmp = LENGTH a /\
                (!i : int.
                   0 <= i /\ i < &(LENGTH tmp) ==>
                   vc_get tmp i = vc_get a i)
                ==>
                (((0 <= (0 : int) /\ 0 <= n) /\
                  vc_sorted_sub ord a 0 0) /\
                 PERM a a) /\
                !first_run : int.
                !tmp1 a1 : 'a list.
                  LENGTH tmp1 = LENGTH tmp ==>
                  LENGTH a1 = LENGTH a ==>
                  (((0 <= first_run /\ first_run <= n) /\
                    vc_sorted_sub ord a1 0 first_run) /\
                   PERM a a1)
                  ==>
                  (((0 <= (0 : int) /\ 0 <= n) /\
                    (first_run <= first_run /\ first_run <= n) /\
                    vc_sorted_sub ord a1 0 first_run /\
                    PERM a1 a1) /\
                   !lo first_run1 : int.
                   !tmp2 a2 : 'a list.
                     LENGTH tmp2 = LENGTH tmp1 ==>
                     LENGTH a2 = LENGTH a1 ==>
                     (0 <= lo /\ lo <= n) /\
                     (first_run <= first_run1 /\ first_run1 <= n) /\
                     vc_sorted_sub ord a2 0 first_run1 /\
                     (lo = 0 \/
                      first_run1 <= lo /\ first_run < first_run1) /\
                     PERM a1 a2
                     ==>
                     if lo < n - 1 then
                       ((0 <= lo /\ lo < &(LENGTH a2)) /\
                        (!mid : int.
                           ((lo < mid /\ mid <= &(LENGTH a2)) /\
                            vc_sorted_sub ord a2 lo mid /\
                            (mid < &(LENGTH a2) ==>
                             ~ord
                               (vc_get a2 (mid - 1))
                               (vc_get a2 mid)))
                           ==>
                           if mid = n then
                             (if lo = 0 then
                                vc_sorted ord a2 /\ PERM a a2
                              else
                                (0 <= n - first_run /\
                                 n - first_run1 < n - first_run) /\
                                (((0 <= first_run1 /\
                                   first_run1 <= n) /\
                                  vc_sorted_sub ord a2 0 first_run1) /\
                                 PERM a a2))
                           else
                             ((0 <= mid /\ mid < &(LENGTH a2)) /\
                              (!hi : int.
                                 ((mid < hi /\ hi <= &(LENGTH a2)) /\
                                  vc_sorted_sub ord a2 mid hi /\
                                  (hi < &(LENGTH a2) ==>
                                   ~ord
                                     (vc_get a2 (hi - 1))
                                     (vc_get a2 hi)))
                                 ==>
                                 (((0 <= lo /\ lo <= mid /\
                                    mid <= hi /\
                                    hi <= &(LENGTH tmp2) /\
                                    LENGTH tmp2 = LENGTH a2) /\
                                   vc_sorted_sub ord a2 lo mid /\
                                   vc_sorted_sub ord a2 mid hi) /\
                                  (!a3 : 'a list.
                                     LENGTH a3 = LENGTH a2 ==>
                                     vc_sorted_sub ord a3 lo hi /\
                                     vc_permut_sub
                                       a2 a3
                                       (vc_to_nat lo)
                                       (vc_to_nat hi) /\
                                     (!i : int.
                                        ((0 <= i /\ i < lo) \/
                                         (hi <= i /\
                                          i < &(LENGTH a3))) ==>
                                        vc_get a3 i = vc_get a2 i)
                                     ==>
                                     if lo = 0 then
                                       (0 <= n - lo /\
                                        n - hi < n - lo) /\
                                       (0 <= hi /\ hi <= n) /\
                                       (first_run <= hi /\ hi <= n) /\
                                       vc_sorted_sub ord a3 0 hi /\
                                       (hi = 0 \/
                                        hi <= hi /\ first_run < hi) /\
                                       PERM a1 a3
                                     else
                                       (0 <= n - lo /\
                                        n - hi < n - lo) /\
                                       (0 <= hi /\ hi <= n) /\
                                       (first_run <= first_run1 /\
                                        first_run1 <= n) /\
                                       vc_sorted_sub ord a3 0 first_run1 /\
                                       (hi = 0 \/
                                        first_run1 <= hi /\
                                        first_run < first_run1) /\
                                       PERM a1 a3))))))
                     else
                       (0 <= n - first_run /\
                        n - first_run1 < n - first_run) /\
                       (((0 <= first_run1 /\ first_run1 <= n) /\
                         vc_sorted_sub ord a2 0 first_run1) /\
                        PERM a a2))``;
