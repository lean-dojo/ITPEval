(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc: the top-level
  quicksort verification condition, stating full-range sortedness and
  permutation of the input integer list. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val verifythis_2021_shearsort_Quicksort_quicksort_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : int list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else 0
    in
    let vc_slice =
      \xs : int list. \lower upper : num.
        TAKE (upper - lower) (DROP lower xs)
    in
    let vc_permut_sub_prime =
      \xs ys : int list. \lower upper : num.
        LENGTH xs = LENGTH ys /\
        vc_slice xs 0 lower = vc_slice ys 0 lower /\
        vc_slice xs upper (LENGTH xs) =
          vc_slice ys upper (LENGTH xs) /\
        PERM
          (vc_slice xs lower upper)
          (vc_slice ys lower upper)
    in
    let vc_sorted_sub =
      \xs : int list. \lower upper : int.
        !i1 i2 : int.
          lower <= i1 /\ i1 <= i2 /\ i2 < upper ==>
          vc_get xs i1 <= vc_get xs i2
    in
    let vc_sorted =
      \xs : int list.
        vc_sorted_sub xs 0 (&(LENGTH xs))
    in
      !a : int list.
        let o1 = &(LENGTH a)
        in
          ((0 : int) <= 0 /\ 0 <= o1 /\ o1 <= &(LENGTH a)) /\
          !a1 : int list.
            LENGTH a1 = LENGTH a ==>
            vc_sorted_sub a1 0 o1 /\
            vc_permut_sub_prime a a1 0 (vc_to_nat o1) ==>
            vc_sorted a1 /\ PERM a a1``;
