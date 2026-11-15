(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/linked_n_before_last_Why3_ide_VClinked_n_before_last_loop_inv_2_preserved_goal7:
  preservation of the linked-list loop invariant when advancing to the next
  array index before the last node. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val linked_n_before_last_Why3_ide_VClinked_n_before_last_loop_inv_2_preserved_goal7 =
  ``let lnb_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lnb_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lnb_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lnb_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lnb_p_linked_n =
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
            mptr (lnb_shift array (index + k)) = roots k /\
            lnb_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lnb_shift (roots k) 0)
    in
      !i_1 i i_2 : int.
      !t_1 : (int # int) -> (int # int).
      !a_2 a a_1 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = 1 + i_1 in
        let x_1 = i + i_2 in
        let a_3 = t_1 (lnb_shift a_2 (i + i_1)) in
        let x_3 = i + i_2 - 1 in
          0 < i_2 ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_2 <= i_1 ==>
          0 <= i_2 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          lnb_framed region t_1 ==>
          linked t ==>
          lnb_is_sint32 i ==>
          lnb_is_sint32 i_1 ==>
          lnb_is_sint32 i_2 ==>
          lnb_is_sint32 (i_2 - 1) ==>
          lnb_is_sint32 x ==>
          lnb_valid_rw t (lnb_shift a_2 0) 2147483646 ==>
          lnb_p_linked_n t t_1 a a_2 i x a_1 ==>
          lnb_p_linked_n t t_1
            (t_1 (lnb_shift a_2 x_1)) a_2 x_1
            (i_1 - i_2) a_3 ==>
          lnb_p_linked_n t t_1
            (t_1 (lnb_shift a_2 x_3)) a_2 x_3
            (1 + i_1 - i_2) a_3``;
