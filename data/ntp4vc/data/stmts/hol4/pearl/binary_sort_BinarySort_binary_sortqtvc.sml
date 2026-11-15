(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_sort_BinarySort_binary_sortqtvc: a binary insertion-sort
  verification condition preserving sorted prefixes and permutation of the
  original integer list. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val binary_sort_vc =
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
    let vc_permut_sub =
      \xs : int list. \ys : int list. \lower : num. \upper : num.
        LENGTH xs = LENGTH ys /\
        vc_slice xs 0 lower = vc_slice ys 0 lower /\
        vc_slice xs upper (LENGTH xs) =
          vc_slice ys upper (LENGTH xs) /\
        PERM (vc_slice xs lower upper) (vc_slice ys lower upper)
    in
      !a : int list.
        let o1 = &(LENGTH a) - 1 in
          (1 <= o1 + 1 ==>
             ((!i j : int.
                 0 <= i /\ i <= j /\ j < 1 ==>
                 vc_get a i <= vc_get a j) /\
              vc_permut_sub a a 0 (LENGTH a)) /\
             !a1 : int list.
               LENGTH a1 = LENGTH a ==>
               ((!k : int.
                   ((1 <= k /\ k <= o1) /\
                    (!i j : int.
                       0 <= i /\ i <= j /\ j < k ==>
                       vc_get a1 i <= vc_get a1 j) /\
                    vc_permut_sub a a1 0 (LENGTH a1)) ==>
                   (0 <= k /\ k < &(LENGTH a1)) /\
                   let v = vc_get a1 k in
                     (((0 <= (0 : int) /\ 0 <= k /\ k <= k) /\
                       (!i : int.
                          0 <= i /\ i < 0 ==>
                          vc_get a1 i <= v) /\
                       (!i : int.
                          k <= i /\ i < k ==>
                          v < vc_get a1 i)) /\
                      !right1 left1 : int.
                        ((0 <= left1 /\ left1 <= right1 /\
                          right1 <= k) /\
                         (!i : int.
                            0 <= i /\ i < left1 ==>
                            vc_get a1 i <= v) /\
                         (!i : int.
                            right1 <= i /\ i < k ==>
                            v < vc_get a1 i)) ==>
                        if left1 < right1 then
                          ~(2 = (0 : int)) /\
                          (let mid =
                             left1 + (right1 - left1) quot 2
                           in
                             (0 <= mid /\ mid < &(LENGTH a1)) /\
                             if v < vc_get a1 mid then
                               (0 <= right1 - left1 /\
                                mid - left1 < right1 - left1) /\
                               (0 <= left1 /\ left1 <= mid /\
                                mid <= k) /\
                               (!i : int.
                                  0 <= i /\ i < left1 ==>
                                  vc_get a1 i <= v) /\
                               (!i : int.
                                  mid <= i /\ i < k ==>
                                  v < vc_get a1 i)
                             else
                               (0 <= right1 - left1 /\
                                right1 - (mid + 1) <
                                  right1 - left1) /\
                               (0 <= mid + 1 /\ mid + 1 <= right1 /\
                                right1 <= k) /\
                               (!i : int.
                                  0 <= i /\ i < mid + 1 ==>
                                  vc_get a1 i <= v) /\
                               (!i : int.
                                  right1 <= i /\ i < k ==>
                                  v < vc_get a1 i))
                        else
                          let o2 = k - left1 in
                          let o3 = left1 + 1 in
                            (((0 <= left1 /\ 0 <= o2 /\
                               left1 + o2 <= &(LENGTH a1)) /\
                              0 <= o3 /\
                              o3 + o2 <= &(LENGTH a1)) /\
                             !a2 : int list.
                               LENGTH a2 = LENGTH a1 ==>
                               ((!i : int.
                                   (0 <= i /\ i < o3 \/
                                    o3 + o2 <= i /\
                                    i < &(LENGTH a2)) ==>
                                   vc_get a2 i = vc_get a1 i) /\
                                (!i : int.
                                   o3 <= i /\ i < o3 + o2 ==>
                                   vc_get a2 i =
                                     vc_get a1 (left1 + i - o3))) ==>
                               (0 <= left1 /\
                                left1 < &(LENGTH a2)) /\
                               (LENGTH
                                  (LUPDATE v (vc_to_nat left1) a2) =
                                  LENGTH a2 ==>
                                (!z : int.
                                   0 <= z /\ z < &(LENGTH a2) ==>
                                   vc_get
                                     (LUPDATE v (vc_to_nat left1) a2)
                                     z =
                                   if z = left1 then v
                                   else vc_get a2 z) ==>
                                (!i j : int.
                                   0 <= i /\ i <= j /\ j < k + 1 ==>
                                   vc_get
                                     (LUPDATE v (vc_to_nat left1) a2)
                                     i <=
                                   vc_get
                                     (LUPDATE v (vc_to_nat left1) a2)
                                     j) /\
                                vc_permut_sub
                                  a
                                  (LUPDATE v (vc_to_nat left1) a2)
                                  0
                                  (LENGTH
                                    (LUPDATE v
                                      (vc_to_nat left1) a2)))))) /\
                (((!i j : int.
                     0 <= i /\ i <= j /\ j < o1 + 1 ==>
                     vc_get a1 i <= vc_get a1 j) /\
                  vc_permut_sub a a1 0 (LENGTH a1)) ==>
                 (!i j : int.
                    0 <= i /\ i <= j /\ j < &(LENGTH a1) ==>
                    vc_get a1 i <= vc_get a1 j) /\
                 vc_permut_sub a a1 0 (LENGTH a1)))) /\
          (o1 + 1 < 1 ==>
             (!i j : int.
                0 <= i /\ i <= j /\ j < &(LENGTH a) ==>
                vc_get a i <= vc_get a j) /\
             vc_permut_sub a a 0 (LENGTH a))``;
