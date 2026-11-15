(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_TopDownMergesort_mergesort_recqtvc: the recursive
  top-down mergesort verification condition over lists ordered by a total
  preorder, preserving sorted subranges, permutations, and elements outside
  the merged range. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val mergesort_array_TopDownMergesort_mergesort_rec_vc =
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
    let vc_permut_sub_prime =
      \xs ys : 'a list. \lower upper : num.
        LENGTH xs = LENGTH ys /\
        vc_slice xs 0 lower = vc_slice ys 0 lower /\
        vc_slice xs upper (LENGTH xs) =
          vc_slice ys upper (LENGTH xs) /\
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
        !l r : int.
        !a tmp : 'a list.
          0 <= l ==>
          l <= r ==>
          r <= &(LENGTH a) ==>
          LENGTH a = LENGTH tmp ==>
          if r - (1 : int) <= l then
            vc_sorted_sub ord a l r /\
            vc_permut_sub_prime
              a a (vc_to_nat l) (vc_to_nat r)
          else
            ~((2 : int) = (0 : int)) /\
            let m = l + (r - l) quot (2 : int)
            in
              (((0 : int) <= r - l /\ m - l < r - l) /\
               (0 : int) <= l /\
               l <= m /\
               m <= &(LENGTH a) /\
               LENGTH a = LENGTH tmp) /\
              (!tmp1 a1 : 'a list.
                 LENGTH tmp1 = LENGTH tmp ==>
                 LENGTH a1 = LENGTH a ==>
                 vc_sorted_sub ord a1 l m /\
                 vc_permut_sub_prime
                   a a1 (vc_to_nat l) (vc_to_nat m) ==>
                 (((0 : int) <= r - l /\ r - m < r - l) /\
                  (0 : int) <= m /\
                  m <= r /\
                  r <= &(LENGTH a1) /\
                  LENGTH a1 = LENGTH tmp1) /\
                 (!tmp2 a2 : 'a list.
                    LENGTH tmp2 = LENGTH tmp1 ==>
                    LENGTH a2 = LENGTH a1 ==>
                    vc_sorted_sub ord a2 m r /\
                    vc_permut_sub_prime
                      a1 a2 (vc_to_nat m) (vc_to_nat r) ==>
                    ((((0 : int) <= l /\
                       l <= m /\
                       m <= r /\
                       r <= &(LENGTH tmp2) /\
                       LENGTH tmp2 = LENGTH a2) /\
                      vc_sorted_sub ord a2 l m /\
                      vc_sorted_sub ord a2 m r) /\
                     (!a3 : 'a list.
                        LENGTH a3 = LENGTH a2 ==>
                        vc_sorted_sub ord a3 l r /\
                        vc_permut_sub
                          a2 a3 (vc_to_nat l) (vc_to_nat r) /\
                        (!i : int.
                           ((0 : int) <= i /\ i < l) \/
                           (r <= i /\ i < &(LENGTH a3)) ==>
                           vc_get a3 i = vc_get a2 i) ==>
                        vc_sorted_sub ord a3 l r /\
                        vc_permut_sub_prime
                          a a3 (vc_to_nat l) (vc_to_nat r)))))``;
