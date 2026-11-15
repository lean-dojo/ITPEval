(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_findqtvc: the recursive verification
  condition for finding an integer value in a nonempty half-open sequence
  interval with a positive occurrence count. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val verifythis_2019_ghc_sort_Top_find_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_nth =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_interval =
      \xs : int list. \lower upper : int.
        TAKE (vc_to_num (upper - lower)) (DROP (vc_to_num lower) xs)
    in
    let vc_occ =
      \value : int. \xs : int list. \lower upper : int.
        &(LENGTH
            (FILTER (\x : int. x = value)
              (vc_interval xs lower upper)))
    in
      !s e : int.
      !seq1 : int list.
      !v : int.
        0 <= s /\
        s < e /\
        e <= &(LENGTH seq1) /\
        1 <= vc_occ v seq1 s e ==>
        let o1 = vc_nth seq1 s
        in
          (~(o1 = v) ==>
            let o2 = s + 1
            in
              (0 <= e - s /\ e - o2 < e - s) /\
              (0 <= o2 /\ o2 < e /\ e <= &(LENGTH seq1)) /\
              1 <= vc_occ v seq1 o2 e) /\
          !result : int.
            (if o1 = v then
               result = s
             else
               (s + 1 <= result /\ result < e) /\
               vc_nth seq1 result = v) ==>
            (s <= result /\ result < e) /\
            vc_nth seq1 result = v``;
