(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_split_segment_right_Why3_ide_VClinked_n_split_segment_right_post_goal0:
  extraction of the length-i prefix from a modeled linked-list segment of
  length i + 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_split_segment_right_Why3_ide_VClinked_n_split_segment_right_post_goal0 =
  ``let lnssr_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnssr_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnssr_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnssr_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnssr_p_linked_n =
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
            mptr (lnssr_shift array (index + k)) = roots k /\
            lnssr_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnssr_shift (roots k) 0)
    in
      !i i_1 : int.
      !t_1 : (int # int) -> (int # int).
      !a_2 a a_1 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_3 =
          t_1
            (lnssr_shift
              (t_1 (lnssr_shift a_2 (i + i_1 - 1))) 0)
        in
          0 < i ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          lnssr_framed region t_1 ==>
          linked t ==>
          lnssr_is_sint32 i ==>
          lnssr_is_sint32 i_1 ==>
          lnssr_valid_rw t (lnssr_shift a_2 0) 2147483646 ==>
          lnssr_p_linked_n t t_1 a a_2 i_1 (1 + i) a_1 ==>
          lnssr_p_linked_n t t_1 a a_2 i_1 i a_3``;
