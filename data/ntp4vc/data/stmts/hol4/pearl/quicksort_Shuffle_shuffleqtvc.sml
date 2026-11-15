(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Shuffle_shuffleqtvc: the shuffle-loop verification
  condition requiring every bounded array swap to preserve permutation of
  the original integer array. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val quicksort_Shuffle_shuffle_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : int list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else 0
    in
    let vc_exchange =
      \before : int list. \after : int list. \i : int. \j : int.
        after =
          LUPDATE (vc_get before i) (vc_to_nat j)
            (LUPDATE (vc_get before j) (vc_to_nat i) before)
    in
      !a : int list.
        let o1 = &(LENGTH a) - 1 in
          (1 <= o1 + 1 ==>
           PERM a a /\
           (!a1 : int list.
              LENGTH a1 = LENGTH a ==>
              !i : int.
                ((1 <= i /\ i <= o1) /\ PERM a a1) ==>
                (let o2 = i + 1 in
                   0 < o2 /\
                   (!o3 : int.
                      0 <= o3 /\ o3 < o2 ==>
                      ((0 <= i /\ i < &(LENGTH a1)) /\
                       0 <= o3 /\ o3 < &(LENGTH a1)) /\
                      (!a2 : int list.
                         LENGTH a2 = LENGTH a1 ==>
                         vc_exchange a1 a2 i o3 ==>
                         PERM a a2))))) /\
          (o1 + 1 < 1 ==> PERM a a)``;
