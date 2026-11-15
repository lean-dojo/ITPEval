(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/algo64_Algo64_quicksortqtvc: a quicksort verification condition in
  which partitioning around the pivot 42 and recursively sorting the two
  subranges yields a sorted permutation of the original subrange. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val quicksort_vc =
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
    let vc_sorted_sub =
      \xs : int list. \lower : int. \upper : int.
        !p q : int.
          lower <= p /\ p <= q /\ q < upper ==>
          vc_get xs p <= vc_get xs q
    in
      !m n : int.
      !a : int list.
        0 <= m ==>
        m <= n ==>
        n < &(LENGTH a) ==>
        if m < n then
          (0 <= m /\ m < n /\ n < &(LENGTH a)) /\
          !j i : int.
          !a1 : int list.
            LENGTH a1 = LENGTH a ==>
            (m <= j /\ j < i /\ i <= n) /\
            vc_permut_sub
              a a1 (vc_to_nat m) (vc_to_nat (n + 1)) /\
            (!r : int.
               m <= r /\ r <= j ==>
               vc_get a1 r <= 42) /\
            (!r : int.
               j < r /\ r < i ==>
               vc_get a1 r = 42) /\
            (!r : int.
               i <= r /\ r <= n ==>
               42 <= vc_get a1 r) ==>
            (((0 <= n - m /\ j - m < n - m) /\
              0 <= m /\ m <= j /\ j < &(LENGTH a1)) /\
             !a2 : int list.
               LENGTH a2 = LENGTH a1 ==>
               vc_permut_sub
                 a1 a2 (vc_to_nat m) (vc_to_nat (j + 1)) /\
               vc_sorted_sub a2 m (j + 1) ==>
               (((0 <= n - m /\ n - i < n - m) /\
                 0 <= i /\ i <= n /\ n < &(LENGTH a2)) /\
                !a3 : int list.
                  LENGTH a3 = LENGTH a2 ==>
                  vc_permut_sub
                    a2 a3 (vc_to_nat i) (vc_to_nat (n + 1)) /\
                  vc_sorted_sub a3 i (n + 1) ==>
                  vc_permut_sub
                    a a3 (vc_to_nat m) (vc_to_nat (n + 1)) /\
                  vc_sorted_sub a3 m (n + 1)))
        else
          vc_permut_sub
            a a (vc_to_nat m) (vc_to_nat (n + 1)) /\
          vc_sorted_sub a m (n + 1)``;
