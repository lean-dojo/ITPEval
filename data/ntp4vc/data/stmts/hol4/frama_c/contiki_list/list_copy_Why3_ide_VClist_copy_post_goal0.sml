(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_copy_Why3_ide_VClist_copy_post_goal0:
  preservation of a modeled linked-list segment after copying a pointer into
  one memory-map location. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_copy_Why3_ide_VClist_copy_post_goal0 =
  ``let lc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lc_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
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
      !a_2 : int # int.
      !t_1 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !t : int -> int.
      !i i_1 : int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_3 = lc_shift a_2 0 in
        let a_4 = t_1 a in
        let m = lc_update t_1 a_1 a_4 in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          lc_framed region t_1 ==>
          linked t ==>
          lc_is_sint32 i ==>
          lc_is_sint32 i_1 ==>
          lc_valid_rw t a 1 ==>
          lc_valid_rw t a_1 1 ==>
          lc_valid_rw t a_3 2147483646 ==>
          lc_separated a_1 1 a_3 2147483646 ==>
          lc_separated (t_1 a_1) 4 a_3 2147483646 ==>
          lc_p_linked_n t t_1 a_4 a_2 i_1 i (0, 0) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < i + i_1 ==>
            lc_separated a_1 1 (t_1 (lc_shift a_2 i_2)) 4) ==>
          lc_p_linked_n t m a_4 a_2 i_1 i (0, 0)``;
