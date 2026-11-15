(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_split_segment_direct_Why3_ide_VClinked_n_split_segment_direct_post_2_goal1:
  extraction of the suffix beginning at a direct split point of a modeled
  linked-list segment. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_split_segment_direct_Why3_ide_VClinked_n_split_segment_direct_post_2_goal1 =
  ``let lnssd_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnssd_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnssd_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnssd_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnssd_p_linked_n =
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
            mptr (lnssd_shift array (index + k)) = roots k /\
            lnssd_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnssd_shift (roots k) 0)
    in
      !i i_2 i_1 : int.
      !t_1 : (int # int) -> (int # int).
      !a_2 a a_1 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i + i_2 in
        let a_3 = t_1 (lnssd_shift a_2 x) in
          0 < i ==>
          0 < i_1 ==>
          0 <= i_2 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          lnssd_framed region t_1 ==>
          linked t ==>
          lnssd_is_sint32 i ==>
          lnssd_is_sint32 i_1 ==>
          lnssd_is_sint32 i_2 ==>
          lnssd_valid_rw t (lnssd_shift a_2 0) 2147483646 ==>
          lnssd_p_linked_n t t_1 a a_2 i_2 (i + i_1) a_1 ==>
          lnssd_p_linked_n t t_1 a_3 a_2 x i_1 a_1``;
