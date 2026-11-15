(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_call_linked_n_before_last_pre_Linked_goal41:
  the linked-list segment condition required before chopping the list just
  before its last node. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_chop_Why3_ide_VClist_chop_call_linked_n_before_last_pre_Linked_goal41 =
  ``let lc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lc_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lc_p_linked_n =
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
            mptr (lc_shift array (index + k)) = roots k /\
            lc_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lc_shift (roots k) 0)
    in
      !i_1 i_2 : int.
      !t_1 : (int # int) -> (int # int).
      !a_1 a : int # int.
      !i : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i_1 + i_2 in
        let a_2 = t_1 (lc_shift a_1 x) in
        let a_3 = t_1 (lc_shift a_2 0) in
        let a_4 = t_1 (lc_shift a_3 0) in
        let a_5 = t_1 a in
        let a_6 = lc_shift a_1 0 in
        let x_1 = i + i_1 in
          a_4 = (0, 0) ==>
          ~(a_4 = a_5) ==>
          ~(a_4 = t_1 (lc_shift a_5 0)) ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          2 + i_2 <= i ==>
          lc_framed region t_1 ==>
          linked t ==>
          lc_is_sint32 i ==>
          lc_is_sint32 i_1 ==>
          lc_is_sint32 i_2 ==>
          lc_valid_rw t a 1 ==>
          lc_valid_rw t a_6 2147483646 ==>
          lc_separated a 1 a_6 2147483646 ==>
          lc_separated a_5 4 a_6 2147483646 ==>
          lc_valid_rw t a_3 4 ==>
          lc_p_linked_n t t_1 a_5 a_1 i_1 i a_4 ==>
          lc_p_linked_n t t_1 a_2 a_1 x (i - i_2) a_4 ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x_1 ==>
            lc_separated a 1 (t_1 (lc_shift a_1 i_3)) 4) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x_1 ==>
            lc_separated (t_1 (lc_shift a_1 i_3)) 4
              a_6 2147483646) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x_1 ==>
            i_4 < x_1 ==>
            ~(t_1 (lc_shift a_1 i_4) =
              t_1 (lc_shift a_1 i_3))) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x_1 ==>
            i_4 < x_1 ==>
            lc_separated (t_1 (lc_shift a_1 i_4)) 4
              (t_1 (lc_shift a_1 i_3)) 4) ==>
          lc_p_linked_n t t_1 a_5 a_1 i_1 (i - 1)
            (t_1 (lc_shift a_1 (i + i_1 - 1)))``;
