(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_preserved_goal12:
  preservation of a linked-list suffix invariant by prepending the final node
  of the split prefix to the remaining segment. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_preserved_goal12 =
  ``let lnss_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnss_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnss_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnss_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnss_p_linked_n =
      \malloc : int -> int.
       \mptr : (int # int) -> (int # int).
       \root : int # int. \array : int # int.
       \index : int. \n : int. \bound : int # int.
        0 <= n /\
        0 <= index /\
        0 <= index + n /\
        index + n <= 2147483646 /\
        ?roots : int -> (int # int).
          roots 0 = root /\
          roots n = bound /\
          !k : int.
            0 <= k /\ k < n ==>
            mptr (lnss_shift array (index + k)) = roots k /\
            lnss_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnss_shift (roots k) 0)
    in
      !i_1 i_3 i i_2 : int.
      !t_1 : (int # int) -> (int # int).
      !a_2 a a_1 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i_1 + i_3 - 1 in
        let a_3 =
          t_1
            (lnss_shift
              (t_1 (lnss_shift a_2 x)) 0)
        in
          0 < i ==>
          i < i_3 ==>
          0 <= i_1 ==>
          i <= i_2 ==>
          i_3 <= i_2 ==>
          i <= i_3 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region
            (FST
              (t_1
                (lnss_shift
                  (t_1 (lnss_shift a_2 (i + i_1 - 1))) 0))) <= 0 ==>
          lnss_framed region t_1 ==>
          linked t ==>
          lnss_is_sint32 i ==>
          lnss_is_sint32 i_1 ==>
          lnss_is_sint32 i_2 ==>
          lnss_is_sint32 i_3 ==>
          lnss_is_sint32 (i_3 - 1) ==>
          lnss_is_sint32 (i_2 - i) ==>
          lnss_valid_rw t (lnss_shift a_2 0) 2147483646 ==>
          lnss_p_linked_n t t_1 a a_2 i_1 i_2 a_1 ==>
          lnss_p_linked_n t t_1 a a_2 i_1 i_3 a_3 ==>
          lnss_p_linked_n t t_1 a_3 a_2 (i_1 + i_3)
            (i_2 - i_3) a_1 ==>
          lnss_p_linked_n t t_1
            (t_1
              (lnss_shift
                (t_1
                  (lnss_shift a_2 (i_1 + i_3 - 2))) 0))
            a_2 x (1 + i_2 - i_3) a_1``;
