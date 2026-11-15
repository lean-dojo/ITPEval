(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc: the verification
  condition carrying ordered monotonic cutpoints through sorted segment
  lists to a sorted permutation preserving the input occurrences and length.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory sortingTheory;

val verifythis_2019_ghc_sort_Top_sort_to_list_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_nth =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_seq =
      \cutpoints : int list. REVERSE cutpoints
    in
    let vc_first =
      \cutpoints : int list. vc_nth (vc_seq cutpoints) 0
    in
    let vc_last =
      \cutpoints : int list.
        vc_nth
          (vc_seq cutpoints)
          (&(LENGTH (vc_seq cutpoints)) - 1)
    in
    let vc_sorted =
      \xs : int list. SORTED (\x y : int. x <= y) xs
    in
    let vc_count =
      \x : int. \xs : int list.
        &(LENGTH (FILTER (\y : int. y = x) xs))
    in
    let vc_map_occ =
      \x : int. \a : int list. \lower upper : int.
        &(CARD
            {i : int |
               lower <= i /\ i < upper /\ vc_nth a i = x})
    in
    let vc_segment =
      \a : int list. \lower upper : int.
        (!z1 z2 : int.
           lower <= z1 /\ z1 < z2 /\ z2 < upper ==>
           vc_nth a z1 < vc_nth a z2) \/
        (!z1 z2 : int.
           lower <= z1 /\ z1 < z2 /\ z2 < upper ==>
           vc_nth a z2 <= vc_nth a z1)
    in
    let vc_all_segments =
      \a cutpoints : int list.
        !k : int.
          0 <= k /\
          k < &(LENGTH (vc_seq cutpoints)) - 1 ==>
          vc_segment
            a
            (vc_nth (vc_seq cutpoints) k)
            (vc_nth (vc_seq cutpoints) (k + 1))
    in
    let vc_seq_sorted =
      \cutpoints : int list.
        !i j : int.
          0 <= i /\
          i < j /\
          j < &(LENGTH (vc_seq cutpoints)) ==>
          vc_nth (vc_seq cutpoints) i <=
          vc_nth (vc_seq cutpoints) j
    in
    let vc_cutpoint_bounds =
      \cutpoints : int list. \upper : int.
        !z : int.
          MEM z cutpoints ==> 0 <= z /\ z <= upper
    in
      !a : int list.
        0 < &(LENGTH a) ==>
        0 < &(LENGTH a) /\
        !cutpoints : int list.
          vc_first cutpoints = 0 /\
          vc_last cutpoints = &(LENGTH a) /\
          (2 : int) <= &(LENGTH cutpoints) /\
          vc_cutpoint_bounds cutpoints (&(LENGTH a)) /\
          vc_all_segments a cutpoints /\
          vc_seq_sorted cutpoints
          ==>
          (0 : int) < &(LENGTH cutpoints) /\
          vc_seq_sorted cutpoints /\
          vc_cutpoint_bounds cutpoints (&(LENGTH a)) /\
          vc_all_segments a cutpoints /\
          !lists : int list list.
            (!l : int list.
               MEM l lists ==> vc_sorted l) /\
            (!x : int.
               vc_count x (FLAT lists) =
               vc_map_occ
                 x a (vc_first cutpoints) (vc_last cutpoints))
            ==>
            (!l : int list.
               MEM l lists ==> vc_sorted l) /\
            !result : int list.
              vc_sorted result /\
              PERM result (FLAT lists)
              ==>
              vc_sorted result /\
              (!x : int.
                 vc_map_occ x a 0 (&(LENGTH a)) =
                 vc_count x result) /\
              LENGTH result = LENGTH a``;
