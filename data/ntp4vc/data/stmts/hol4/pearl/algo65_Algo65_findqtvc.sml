(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/algo65_Algo65_findqtvc: a selection-algorithm verification condition
  in which partitioning around 42 and recursively processing the side
  containing index k yields a subrange permutation whose kth entry separates
  the subrange. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val find_vc =
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
      !m k n : int.
      !a : int list.
        0 <= m ==>
        m <= k ==>
        k <= n ==>
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
            if k <= j then
              (((0 <= n - m /\ j - m < n - m) /\
                0 <= m /\ m <= k /\ k <= j /\
                j < &(LENGTH a1)) /\
               !a2 : int list.
                 LENGTH a2 = LENGTH a1 ==>
                 vc_permut_sub
                   a1 a2 (vc_to_nat m) (vc_to_nat (j + 1)) /\
                 (!r : int.
                    m <= r /\ r <= k ==>
                    vc_get a2 r <= vc_get a2 k) /\
                 (!r : int.
                    k <= r /\ r <= j ==>
                    vc_get a2 k <= vc_get a2 r) ==>
                 if i <= k then
                   (((0 <= n - m /\ n - i < n - m) /\
                     0 <= i /\ i <= k /\ k <= n /\
                     n < &(LENGTH a2)) /\
                    !a3 : int list.
                      LENGTH a3 = LENGTH a2 ==>
                      vc_permut_sub
                        a2 a3 (vc_to_nat i) (vc_to_nat (n + 1)) /\
                      (!r : int.
                         i <= r /\ r <= k ==>
                         vc_get a3 r <= vc_get a3 k) /\
                      (!r : int.
                         k <= r /\ r <= n ==>
                         vc_get a3 k <= vc_get a3 r) ==>
                      vc_permut_sub
                        a a3 (vc_to_nat m) (vc_to_nat (n + 1)) /\
                      (!r : int.
                         m <= r /\ r <= k ==>
                         vc_get a3 r <= vc_get a3 k) /\
                      (!r : int.
                         k <= r /\ r <= n ==>
                         vc_get a3 k <= vc_get a3 r))
                 else
                   vc_permut_sub
                     a a2 (vc_to_nat m) (vc_to_nat (n + 1)) /\
                   (!r : int.
                      m <= r /\ r <= k ==>
                      vc_get a2 r <= vc_get a2 k) /\
                   (!r : int.
                      k <= r /\ r <= n ==>
                      vc_get a2 k <= vc_get a2 r))
            else if i <= k then
              (((0 <= n - m /\ n - i < n - m) /\
                0 <= i /\ i <= k /\ k <= n /\
                n < &(LENGTH a1)) /\
               !a2 : int list.
                 LENGTH a2 = LENGTH a1 ==>
                 vc_permut_sub
                   a1 a2 (vc_to_nat i) (vc_to_nat (n + 1)) /\
                 (!r : int.
                    i <= r /\ r <= k ==>
                    vc_get a2 r <= vc_get a2 k) /\
                 (!r : int.
                    k <= r /\ r <= n ==>
                    vc_get a2 k <= vc_get a2 r) ==>
                 vc_permut_sub
                   a a2 (vc_to_nat m) (vc_to_nat (n + 1)) /\
                 (!r : int.
                    m <= r /\ r <= k ==>
                    vc_get a2 r <= vc_get a2 k) /\
                 (!r : int.
                    k <= r /\ r <= n ==>
                    vc_get a2 k <= vc_get a2 r))
            else
              vc_permut_sub
                a a1 (vc_to_nat m) (vc_to_nat (n + 1)) /\
              (!r : int.
                 m <= r /\ r <= k ==>
                 vc_get a1 r <= vc_get a1 k) /\
              (!r : int.
                 k <= r /\ r <= n ==>
                 vc_get a1 k <= vc_get a1 r)
        else
          vc_permut_sub
            a a (vc_to_nat m) (vc_to_nat (n + 1)) /\
          (!r : int.
             m <= r /\ r <= k ==>
             vc_get a r <= vc_get a k) /\
          (!r : int.
             k <= r /\ r <= n ==>
             vc_get a k <= vc_get a r)``;
