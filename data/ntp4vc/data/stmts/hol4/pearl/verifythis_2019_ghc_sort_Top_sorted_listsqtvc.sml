(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc: the recursive
  verification condition for turning monotonic integer-list segments
  delimited by ordered cutpoints into nondecreasing lists while preserving
  occurrence counts across the covered interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pred_setTheory sortingTheory;

val verifythis_2019_ghc_sort_Top_sorted_lists_vc =
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
    let vc_count =
      \x : int. \xs : int list.
        &(LENGTH (FILTER (\y : int. y = x) xs))
    in
    let vc_map_occ =
      \x : int. \s : int list. \lower upper : int.
        &(CARD
            {i : int |
               lower <= i /\
               i < upper /\
               vc_nth s i = x})
    in
    let vc_strict =
      \xs : int list. SORTED (\x y : int. x < y) xs
    in
    let vc_increasing =
      \xs : int list. SORTED (\x y : int. x <= y) xs
    in
    let vc_decreasing =
      \xs : int list. SORTED (\x y : int. y <= x) xs
    in
    let vc_strict_segment =
      \s : int list. \lower upper : int.
        !z1 z2 : int.
          lower <= z1 /\
          z1 < z2 /\
          z2 < upper ==>
          vc_nth s z1 < vc_nth s z2
    in
    let vc_decreasing_segment =
      \s : int list. \lower upper : int.
        !z1 z2 : int.
          lower <= z1 /\
          z1 < z2 /\
          z2 < upper ==>
          vc_nth s z2 <= vc_nth s z1
    in
    let vc_segment =
      \s : int list. \lower upper : int.
        vc_strict_segment s lower upper \/
        vc_decreasing_segment s lower upper
    in
    let vc_precondition =
      \s cutp : int list.
        0 < &(LENGTH cutp) /\
        (!x y : int.
           0 <= x /\
           x < y /\
           y < &(LENGTH (vc_seq cutp)) ==>
           vc_nth (vc_seq cutp) x <= vc_nth (vc_seq cutp) y) /\
        (!z : int.
           MEM z cutp ==> 0 <= z /\ z <= &(LENGTH s)) /\
        (!k : int.
           0 <= k /\
           k < &(LENGTH (vc_seq cutp)) - 1 ==>
           let ck = vc_nth (vc_seq cutp) k
           in
           let ck1 = vc_nth (vc_seq cutp) (k + 1)
           in
             vc_segment s ck ck1)
    in
    let vc_segment_spec =
      \s : int list. \lower upper : int. \seqi : int list.
        (!x : int.
           vc_count x seqi = vc_map_occ x s lower upper) /\
        (!x : int.
           MEM x seqi ==>
           ?z : int.
             (lower <= z /\ z < upper) /\
             vc_nth s z = x) /\
        (vc_strict_segment s lower upper ==> vc_strict seqi) /\
        (vc_decreasing_segment s lower upper ==> vc_decreasing seqi) /\
        (vc_strict seqi \/ vc_decreasing seqi)
    in
    let vc_slice_spec =
      \whole : int list. \upper : int. \part : int list.
        &(LENGTH part) = upper - 0 /\
        (!k : int.
           0 <= k /\ k < upper - 0 ==>
           vc_nth part k = vc_nth whole (0 + k))
    in
    let vc_result_spec =
      \s cutseq : int list. \result : int list list.
        (!l : int list.
           MEM l result ==> vc_increasing l) /\
        (!x : int.
           vc_count x (FLAT result) =
           vc_map_occ
             x
             s
             (vc_nth cutseq 0)
             (vc_nth cutseq (&(LENGTH cutseq) - 1)))
    in
    let vc_order =
      \xs : int list.
        case xs of
          [] => xs
        | h1::rest =>
            case rest of
              [] => xs
            | h2::tail =>
                if h1 < h2 then xs else REVERSE xs
    in
    let vc_recursive_obligation =
      \s cutp : int list.
        let ls = cutp
        in
        let seq1 = vc_seq cutp
        in
          case ls of
            [] => T
          | h1::rest =>
              case rest of
                [] => T
              | h2::t =>
                  ((0 <= h2 /\ h2 <= &(LENGTH s)) /\
                   (0 <= h1 /\ h1 <= &(LENGTH s)) /\
                   vc_segment s h2 h1) /\
                  (!seqi : int list.
                     vc_segment_spec s h2 h1 seqi ==>
                     let o1 = &(LENGTH seq1) - 1
                     in
                       (0 <= 0 /\ 0 <= o1 /\
                        o1 <= &(LENGTH seq1)) /\
                       (let o2 = TAKE (vc_to_num o1) seq1
                        in
                          vc_slice_spec seq1 o1 o2 ==>
                          let o3 = h2::t
                          in
                            o2 = REVERSE o3 /\
                            (!lseq : int list.
                               lseq = o3 /\ vc_seq lseq = o2 ==>
                               ((case cutp of
                                   [] => F
                                 | _::f => f = lseq) /\
                                vc_precondition s lseq) /\
                               (!o4 : int list list.
                                  vc_result_spec s (vc_seq lseq) o4 ==>
                                  vc_strict seqi \/
                                  vc_decreasing seqi))))
    in
    let vc_result_obligation =
      \s cutp : int list.
        let ls = cutp
        in
        let seq1 = vc_seq cutp
        in
          !result : int list list.
            (case ls of
               [] => result = []
             | h1::rest =>
                 case rest of
                   [] => result = []
                 | h2::t =>
                     ?seqi : int list.
                       vc_segment_spec s h2 h1 seqi /\
                       (let o1 = &(LENGTH seq1) - 1
                        in
                        let o2 = TAKE (vc_to_num o1) seq1
                        in
                          vc_slice_spec seq1 o1 o2 /\
                          (?lseq : int list.
                             (lseq = h2::t /\ vc_seq lseq = o2) /\
                             (?o3 : int list list.
                                vc_result_spec
                                  s (vc_seq lseq) o3 /\
                                (let o4 = vc_order seqi
                                 in
                                   (vc_increasing o4 /\
                                    PERM seqi o4) /\
                                   result = o4::o3)))))
            ==>
            vc_result_spec s (vc_seq cutp) result
    in
      !cutp s : int list.
        vc_precondition s cutp ==>
        vc_recursive_obligation s cutp /\
        vc_result_obligation s cutp``;
