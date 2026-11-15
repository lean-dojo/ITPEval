(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_more_post_3_part3_goal54:
  preservation of a linked-list segment of length i - 1 after a pointer-memory
  update, under the bounds, validity, and separation conditions for list_chop.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_chop_Why3_ide_VClist_chop_more_post_3_part3_goal54 =
  ``let lc54_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lc54_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lc54_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lc54_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lc54_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lc54_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lc54_p_linked_n =
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
            mptr (lc54_shift array (index + k)) = roots k /\
            lc54_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lc54_shift (roots k) 0)
    in
      !i_1 i_2 : int.
      !t_1 : (int # int) -> (int # int).
      !a_1 a : int # int.
      !i : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i_1 + i_2 in
        let a_2 = t_1 (lc54_shift a_1 x) in
        let a_3 = lc54_shift a_2 0 in
        let a_4 = t_1 a_3 in
        let a_5 = t_1 (lc54_shift a_4 0) in
        let a_6 = t_1 a in
        let a_7 = lc54_shift a_1 0 in
        let x_1 = i - 1 in
        let x_2 = i + i_1 in
        let m = lc54_update t_1 a_3 a_5 in
          a_5 = (0, 0) ==>
          ~(a_5 = a_6) ==>
          ~(a_5 = t_1 (lc54_shift a_6 0)) ==>
          0 <= i_1 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          2 <= i ==>
          2 + i_2 <= i ==>
          lc54_framed region t_1 ==>
          linked t ==>
          lc54_is_sint32 i ==>
          lc54_is_sint32 i_1 ==>
          lc54_is_sint32 i_2 ==>
          lc54_valid_rw t a 1 ==>
          lc54_valid_rw t a_7 2147483646 ==>
          lc54_separated a 1 a_7 2147483646 ==>
          lc54_separated a_6 4 a_7 2147483646 ==>
          lc54_valid_rw t a_4 4 ==>
          lc54_p_linked_n t t_1 a_6 a_1 i_1 (i - 2)
            (t_1 (lc54_shift a_1 (i + i_1 - 2))) ==>
          lc54_p_linked_n t t_1 a_6 a_1 i_1 x_1
            (t_1 (lc54_shift a_1 (i + i_1 - 1))) ==>
          lc54_p_linked_n t t_1 a_6 a_1 i_1 i a_5 ==>
          lc54_p_linked_n t t_1 a_2 a_1 x (i - i_2) a_5 ==>
          (!i_3 : int.
            i_1 <= i_3 ==>
            i_3 < x_2 ==>
            lc54_separated a 1 (t_1 (lc54_shift a_1 i_3)) 4) ==>
          (!i_3 : int.
            i_1 <= i_3 ==>
            i_3 < x_2 ==>
            lc54_separated (t_1 (lc54_shift a_1 i_3)) 4
              a_7 2147483646) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x_2 ==>
            i_4 < x_2 ==>
            ~(t_1 (lc54_shift a_1 i_4) =
              t_1 (lc54_shift a_1 i_3))) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x_2 ==>
            i_4 < x_2 ==>
            lc54_separated (t_1 (lc54_shift a_1 i_4)) 4
              (t_1 (lc54_shift a_1 i_3)) 4) ==>
          lc54_p_linked_n t m (m a) a_1 i_1 x_1 a_5``;
