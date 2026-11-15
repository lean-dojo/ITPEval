(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_merge_segment_right_Why3_ide_VClinked_n_merge_segment_right_post_goal0:
  composition of a modeled linked-list segment with the one-node segment
  immediately to its right. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_merge_segment_right_Why3_ide_VClinked_n_merge_segment_right_post_goal0 =
  ``let lnmsr_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnmsr_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnmsr_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnmsr_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnmsr_p_linked_n =
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
            mptr (lnmsr_shift array (index + k)) = roots k /\
            lnmsr_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnmsr_shift (roots k) 0)
    in
      !i i_1 : int.
      !a a_1 a_2 a_3 : int # int.
      !t_1 : (int # int) -> (int # int).
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        0 <= i ==>
        region (FST a) <= 0 ==>
        region (FST a_1) <= 0 ==>
        region (FST a_2) <= 0 ==>
        region (FST a_3) <= 0 ==>
        lnmsr_framed region t_1 ==>
        linked t ==>
        lnmsr_is_sint32 i ==>
        lnmsr_is_sint32 i_1 ==>
        lnmsr_valid_rw t (lnmsr_shift a_3 0) 2147483646 ==>
        lnmsr_p_linked_n t t_1 a a_3 i_1 i a_2 ==>
        lnmsr_p_linked_n t t_1 a_2 a_3 (i + i_1) 1 a_1 ==>
        lnmsr_p_linked_n t t_1 a a_3 i_1 (1 + i) a_1``;
