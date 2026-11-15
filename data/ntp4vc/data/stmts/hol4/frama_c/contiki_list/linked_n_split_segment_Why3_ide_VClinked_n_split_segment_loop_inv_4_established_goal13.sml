(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_established_goal13:
  establishment of a zero-length modeled linked-list segment at the successor
  of the final node of a nonempty segment. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_established_goal13 =
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
      !i i_1 i_2 : int.
      !a a_1 a_2 : int # int.
      !t_1 : (int # int) -> (int # int).
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i + i_1 in
          0 < i ==>
          0 <= i_1 ==>
          0 <= i_2 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region
            (FST
              (t_1
                (lnss_shift
                  (t_1 (lnss_shift a_2 (i + i_2 - 1))) 0))) <= 0 ==>
          lnss_framed region t_1 ==>
          linked t ==>
          lnss_is_sint32 i ==>
          lnss_is_sint32 i_1 ==>
          lnss_is_sint32 i_2 ==>
          lnss_is_sint32 x ==>
          lnss_valid_rw t (lnss_shift a_2 0) 2147483646 ==>
          lnss_p_linked_n t t_1 a a_2 i_2 x a_1 ==>
          lnss_p_linked_n t t_1
            (t_1
              (lnss_shift
                (t_1
                  (lnss_shift a_2 (i + i_1 + i_2 - 1))) 0))
            a_2 (i + i_1 + i_2) 0 a_1``;
