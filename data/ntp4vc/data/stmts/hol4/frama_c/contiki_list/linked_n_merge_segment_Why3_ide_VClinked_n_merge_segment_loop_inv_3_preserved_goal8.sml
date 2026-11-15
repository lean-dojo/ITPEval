(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_3_preserved_goal8:
  preservation of a linked-list prefix invariant by deriving the
  one-node-shorter segment from the current segment decomposition.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_3_preserved_goal8 =
  ``let lnms_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnms_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnms_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnms_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnms_p_linked_n =
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
            mptr (lnms_shift array (index + k)) = roots k /\
            lnms_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnms_shift (roots k) 0)
    in
      !i_3 i_1 i_2 i : int.
      !t_1 : (int # int) -> (int # int).
      !a_3 a a_1 a_2 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i_3 - 1 in
        let a_4 =
          t_1
            (lnms_shift
              (t_1 (lnms_shift a_3 (i_1 + i_3 - 1))) 0)
        in
          ~(i_2 = 0) ==>
          0 < i_3 ==>
          0 <= i ==>
          0 <= i_2 ==>
          i_3 <= i_2 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          2 <= i_3 ==>
          lnms_framed region t_1 ==>
          linked t ==>
          lnms_is_sint32 i ==>
          lnms_is_sint32 i_1 ==>
          lnms_is_sint32 i_2 ==>
          lnms_is_sint32 i_3 ==>
          lnms_is_sint32 x ==>
          lnms_valid_rw t (lnms_shift a_3 0) 2147483646 ==>
          lnms_p_linked_n t t_1 a a_3 i_1 i_2 a_2 ==>
          lnms_p_linked_n t t_1 a_2 a_3 (i_1 + i_2) i a_1 ==>
          lnms_p_linked_n t t_1 a a_3 i_1 i_3 a_4 ==>
          lnms_p_linked_n t t_1 a_4 a_3 (i_1 + i_3)
            (i + i_2 - i_3) a_1 ==>
          lnms_p_linked_n t t_1 a a_3 i_1 x
            (t_1
              (lnms_shift
                (t_1 (lnms_shift a_3 (i_1 + i_3 - 2))) 0))``;
