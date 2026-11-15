(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_cutpointsqtvc: the verification
  condition for computing ordered cutpoints that partition a nonempty
  integer sequence into monotonic segments. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val verifythis_2019_ghc_sort_Top_cutpoints_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_nth =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_seq =
      \cut : int list. REVERSE cut
    in
    let vc_last =
      \cut : int list.
        vc_nth (vc_seq cut) (&(LENGTH (vc_seq cut)) - 1)
    in
    let vc_eqb =
      \b1 b2 : bool. (b1 <=> b2)
    in
    let vc_segment =
      \s : int list. \lo hi : int.
        (!z1 z2 : int.
           lo <= z1 /\ z1 < z2 /\ z2 < hi ==>
           vc_nth s z1 < vc_nth s z2) \/
        (!z1 z2 : int.
           lo <= z1 /\ z1 < z2 /\ z2 < hi ==>
           vc_nth s z2 <= vc_nth s z1)
    in
    let vc_segments =
      \s cut : int list.
        !k : int.
          0 <= k /\ k < &(LENGTH (vc_seq cut)) - 1 ==>
          vc_segment s
            (vc_nth (vc_seq cut) k)
            (vc_nth (vc_seq cut) (k + 1))
    in
    let vc_ordered =
      \cut : int list.
        !i j : int.
          0 <= i /\ i < j /\ j < &(LENGTH (vc_seq cut)) ==>
          vc_nth (vc_seq cut) i <= vc_nth (vc_seq cut) j
    in
    let vc_bounded =
      \n : int. \cut : int list.
        !z : int. MEM z cut ==> 0 <= z /\ z <= n
    in
    let vc_loop_state =
      \s : int list. \n : int. \cut : int list. \endpoint : int.
        (0 < endpoint + 1 /\ endpoint + 1 <= n + 1) /\
        0 < &(LENGTH (vc_seq cut)) /\
        vc_nth (vc_seq cut) 0 = 0 /\
        vc_last cut = endpoint /\
        vc_bounded n cut /\
        vc_segments s cut /\
        vc_ordered cut
    in
    let vc_loop_invariant =
      \s : int list. \n : int. \cut : int list.
        vc_loop_state s n cut (vc_last cut)
    in
    let vc_post =
      \s cut : int list.
        vc_nth (vc_seq cut) 0 = 0 /\
        vc_last cut = &(LENGTH s) /\
        (2 : int) <= &(LENGTH cut) /\
        vc_bounded (&(LENGTH s)) cut /\
        vc_segments s cut /\
        vc_ordered cut
    in
      !s : int list.
        0 < &(LENGTH s) ==>
        let n = &(LENGTH s)
        in
          !o1 : int list.
            o1 = [0] ==>
            ((1 : int) = 0 + 1 /\
             vc_loop_state s n o1 0) /\
            !cut : int list.
              vc_loop_invariant s n cut ==>
              let x = vc_last cut
              in
                if x + 1 < n then
                  ((0 <= x + 1 /\ x + 1 < &(LENGTH s)) /\
                   (0 <= x /\ x < &(LENGTH s))) /\
                  (((x + 1 <= x + 1 /\ x + 1 <= n) /\
                    vc_segment s x (x + 1)) /\
                   !y : int.
                     ((x + 1 <= y /\ y <= n) /\
                      vc_segment s x y) ==>
                     (y < n ==>
                       ((0 <= y /\ y < &(LENGTH s)) /\
                        (let previous = y - 1
                         in
                           0 <= previous /\
                           previous < &(LENGTH s)))) /\
                     !direction_same : bool.
                       (if y < n then
                          let next_direction =
                            (vc_nth s (y - 1) < vc_nth s y)
                          in
                            direction_same =
                              vc_eqb next_direction
                                (vc_nth s x < vc_nth s (x + 1)) /\
                            ((direction_same = T) <=>
                             (next_direction =
                                (vc_nth s x < vc_nth s (x + 1))))
                        else
                          direction_same = F) ==>
                       if direction_same then
                         (0 <= n - y /\
                          n - (y + 1) < n - y) /\
                         (x + 1 <= y + 1 /\ y + 1 <= n) /\
                         vc_segment s x (y + 1)
                       else
                         !extended : int list.
                           extended = y::cut ==>
                           (0 <= n - (x + 1) /\
                            n - (y + 1) < n - (x + 1)) /\
                           vc_loop_state s n extended y)
                else if x < n then
                  !finished : int list.
                    finished = n::cut ==>
                    vc_post s finished
                else
                  vc_post s cut``;
