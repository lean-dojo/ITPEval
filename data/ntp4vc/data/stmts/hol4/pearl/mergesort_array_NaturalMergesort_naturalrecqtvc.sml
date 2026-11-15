(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_naturalrecqtvc: the recursive
  natural-mergesort verification condition over lists ordered by a total
  preorder, preserving sorted subranges, permutations, and unchanged
  elements outside merged ranges. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val mergesort_array_NaturalMergesort_naturalrec_vc =
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
        !lo : int.
        !a tmp : 'a list.
        !k : int.
          0 <= lo ==>
          lo <= &(LENGTH a) ==>
          LENGTH a = LENGTH tmp ==>
          0 <= k ==>
          let n = &(LENGTH a)
          in
            if n - 1 <= lo then
              (n = &(LENGTH a) \/
               lo + k < n /\ n < &(LENGTH a)) /\
              vc_sorted_sub ord a lo n /\
              vc_permut_sub_prime
                a a (vc_to_nat lo) (LENGTH a)
            else
              (0 <= lo /\ lo < &(LENGTH a)) /\
              (!o1 : int.
                 ((lo < o1 /\ o1 <= &(LENGTH a)) /\
                  vc_sorted_sub ord a lo o1 /\
                  (o1 < &(LENGTH a) ==>
                   ~ord
                     (vc_get a (o1 - 1))
                     (vc_get a o1))) ==>
                 if o1 = n then
                   (n = &(LENGTH a) \/
                    lo + k < n /\ n < &(LENGTH a)) /\
                   vc_sorted_sub ord a lo n /\
                   vc_permut_sub_prime
                     a a (vc_to_nat lo) (LENGTH a)
                 else
                   let o2 = k - 1
                   in
                     (0 <= o2 + 1 ==>
                      ((lo + 0 < o1 /\ o1 < n) /\
                       vc_sorted_sub ord a lo o1 /\
                       vc_permut_sub_prime
                         a a (vc_to_nat lo) (LENGTH a)) /\
                      (!mid : int.
                       !a1 tmp1 : 'a list.
                         LENGTH a1 = LENGTH a ==>
                         LENGTH tmp1 = LENGTH tmp ==>
                         ((!i : int.
                            ((0 <= i /\ i <= o2) /\
                             (lo + i < mid /\ mid < n) /\
                             vc_sorted_sub ord a1 lo mid /\
                             vc_permut_sub_prime
                               a a1
                               (vc_to_nat lo)
                               (LENGTH a1) /\
                             (!j : int.
                                0 <= j /\ j < lo ==>
                                vc_get a1 j = vc_get a j)) ==>
                            (((0 <= k /\ i < k) /\
                              (0 <= mid /\
                               mid <= &(LENGTH a1) /\
                               LENGTH a1 = LENGTH tmp1) /\
                              0 <= i) /\
                             (!a2 tmp2 : 'a list.
                                LENGTH a2 = LENGTH a1 ==>
                                LENGTH tmp2 = LENGTH tmp1 ==>
                                (!hi : int.
                                   ((hi = &(LENGTH a2) \/
                                     mid + i < hi /\
                                     hi < &(LENGTH a2)) /\
                                    vc_sorted_sub ord a2 mid hi /\
                                    vc_permut_sub_prime
                                      a1 a2
                                      (vc_to_nat mid)
                                      (LENGTH a2) /\
                                    (!j : int.
                                       0 <= j /\ j < mid ==>
                                       vc_get a2 j =
                                         vc_get a1 j)) ==>
                                   (((0 <= lo /\
                                      lo <= mid /\
                                      mid <= hi /\
                                      hi <= &(LENGTH tmp2) /\
                                      LENGTH tmp2 = LENGTH a2) /\
                                     vc_sorted_sub ord a2 lo mid /\
                                     vc_sorted_sub ord a2 mid hi) /\
                                    (!a3 : 'a list.
                                       LENGTH a3 = LENGTH a2 ==>
                                       (vc_sorted_sub ord a3 lo hi /\
                                        vc_permut_sub
                                          a2 a3
                                          (vc_to_nat lo)
                                          (vc_to_nat hi) /\
                                        (!i1 : int.
                                           ((0 <= i1 /\ i1 < lo) \/
                                            (hi <= i1 /\
                                             i1 <
                                               &(LENGTH a3))) ==>
                                           vc_get a3 i1 =
                                             vc_get a2 i1)) ==>
                                       if hi = n then
                                         (n = &(LENGTH a3) \/
                                          lo + k < n /\
                                          n < &(LENGTH a3)) /\
                                         vc_sorted_sub ord a3 lo n /\
                                         vc_permut_sub_prime
                                           a a3
                                           (vc_to_nat lo)
                                           (LENGTH a3) /\
                                         (!j : int.
                                            0 <= j /\ j < lo ==>
                                            vc_get a3 j =
                                              vc_get a j)
                                       else
                                         (lo + (i + 1) < hi /\
                                          hi < n) /\
                                         vc_sorted_sub
                                           ord a3 lo hi /\
                                         vc_permut_sub_prime
                                           a a3
                                           (vc_to_nat lo)
                                           (LENGTH a3) /\
                                         (!j : int.
                                            0 <= j /\ j < lo ==>
                                            vc_get a3 j =
                                              vc_get a j)))))))
                          /\
                          (((lo + (o2 + 1) < mid /\
                             mid < n) /\
                            vc_sorted_sub ord a1 lo mid /\
                            vc_permut_sub_prime
                              a a1
                              (vc_to_nat lo)
                              (LENGTH a1) /\
                            (!j : int.
                               0 <= j /\ j < lo ==>
                               vc_get a1 j = vc_get a j)) ==>
                           (mid = &(LENGTH a1) \/
                            lo + k < mid /\
                            mid < &(LENGTH a1)) /\
                           vc_sorted_sub ord a1 lo mid /\
                           vc_permut_sub_prime
                             a a1
                             (vc_to_nat lo)
                             (LENGTH a1) /\
                           (!j : int.
                              0 <= j /\ j < lo ==>
                              vc_get a1 j = vc_get a j))))
                     /\
                     (o2 + 1 < 0 ==>
                      (o1 = &(LENGTH a) \/
                       lo + k < o1 /\ o1 < &(LENGTH a)) /\
                      vc_sorted_sub ord a lo o1 /\
                      vc_permut_sub_prime
                        a a (vc_to_nat lo) (LENGTH a)))``;
