(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_Merge_merge_usingqtvc: a merge-step verification
  condition over list subranges ordered by a total preorder, preserving
  sortedness, permutation, copied temporary storage, and values outside the
  merged range. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val mergesort_array_Merge_merge_using_vc =
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
      !ord : 'a -> 'a -> bool.
        ((!x : 'a. ord x x) /\
         (!x y z : 'a. ord x y /\ ord y z ==> ord x z) /\
         (!x y : 'a. ord x y \/ ord y x)) ==>
        !l m r : int.
        !tmp a : 'a list.
        !o1 : bool.
          0 <= l ==>
          l <= m ==>
          m <= r ==>
          r <= &(LENGTH tmp) ==>
          LENGTH tmp = LENGTH a ==>
          vc_sorted_sub ord a l m ==>
          vc_sorted_sub ord a m r ==>
          (if l < m then
             o1 = (if m < r then T else F)
           else
             o1 = F) ==>
          if o1 then
            (0 <= m /\ m < &(LENGTH a)) /\
            let o2 = m - 1
            in
              (0 <= o2 /\ o2 < &(LENGTH a)) /\
              if ord (vc_get a o2) (vc_get a m) then
                vc_sorted_sub ord a l r /\
                vc_permut_sub
                  a a (vc_to_nat l) (vc_to_nat r)
              else
                let o3 = r - l
                in
                  (((0 <= l /\ 0 <= o3 /\
                     l + o3 <= &(LENGTH a)) /\
                    0 <= l /\
                    l + o3 <= &(LENGTH tmp)) /\
                   !tmp1 : 'a list.
                     LENGTH tmp1 = LENGTH tmp ==>
                     ((!i : int.
                         ((0 <= i /\ i < l) \/
                          (l + o3 <= i /\
                           i < &(LENGTH tmp1))) ==>
                         vc_get tmp1 i = vc_get tmp i) /\
                      (!i : int.
                         l <= i /\ i < l + o3 ==>
                         vc_get tmp1 i =
                           vc_get a (l + i - l))) ==>
                     (((0 <= l /\ l <= m /\ m <= r /\
                        r <= &(LENGTH tmp1) /\
                        LENGTH tmp1 = LENGTH a) /\
                       vc_sorted_sub ord tmp1 l m /\
                       vc_sorted_sub ord tmp1 m r) /\
                      !a1 : 'a list.
                        LENGTH a1 = LENGTH a ==>
                        (vc_sorted_sub ord a1 l r /\
                         vc_permut_sub
                           tmp1 a1
                           (vc_to_nat l)
                           (vc_to_nat r) /\
                         (!i : int.
                            ((0 <= i /\ i < l) \/
                             (r <= i /\
                              i < &(LENGTH a1))) ==>
                            vc_get a1 i = vc_get a i)) ==>
                        vc_sorted_sub ord a1 l r /\
                        vc_permut_sub
                          a a1
                          (vc_to_nat l)
                          (vc_to_nat r) /\
                        (!i : int.
                           ((0 <= i /\ i < l) \/
                            (r <= i /\ i < &(LENGTH a1))) ==>
                           vc_get a1 i = vc_get a i)))
          else
            vc_sorted_sub ord a l r /\
            vc_permut_sub
              a a (vc_to_nat l) (vc_to_nat r)``;
