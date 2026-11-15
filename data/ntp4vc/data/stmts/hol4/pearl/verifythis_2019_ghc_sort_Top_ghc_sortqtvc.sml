(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc: the final GHC-sort
  verification condition that copying a nondecreasing integer list with the
  input occurrence counts into an array yields a sorted permutation of the
  input. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory sortingTheory;

val verifythis_2019_ghc_sort_Top_ghc_sort_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_nth =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_map_occ =
      \value : int.
       \xs : int list.
       \lower : int.
       \upper : int.
        &(CARD
          {i : int |
             lower <= i /\
             i < upper /\
             vc_nth xs i = value})
    in
    let vc_count =
      \value : int. \xs : int list.
        &(LENGTH (FILTER (\x : int. x = value) xs))
    in
    let vc_list_sorted =
      \xs : int list. SORTED (\x y : int. x <= y) xs
    in
    let vc_array_sorted =
      \xs : int list.
        !i1 i2 : int.
          0 <= i1 /\
          i1 <= i2 /\
          i2 < &(LENGTH xs) ==>
          vc_nth xs i1 <= vc_nth xs i2
    in
      !a : int list.
        if &(LENGTH a) = 0 then
          vc_array_sorted a /\ PERM a a
        else
          0 < &(LENGTH a) /\
          (!l : int list.
             vc_list_sorted l /\
             (!x : int.
                vc_map_occ x a 0 (&(LENGTH a)) =
                vc_count x l) /\
             LENGTH l = LENGTH a ==>
             ((0 <= (0 : int) /\
               &(LENGTH l) = &(LENGTH a) - 0) /\
              (!a1 : int list.
                 LENGTH a1 = LENGTH a ==>
                 ((!x : int.
                     0 <= x /\ x < &(LENGTH a1) ==>
                     vc_nth a1 x = vc_nth l (x - 0)) /\
                  (!x : int.
                     0 <= x /\ x < 0 ==>
                     vc_nth a1 x = vc_nth a x) /\
                  (!x : int.
                     vc_map_occ x a1 0 (&(LENGTH a1)) =
                     vc_count x l)) ==>
                 vc_array_sorted a1 /\ PERM a1 a)))``;
