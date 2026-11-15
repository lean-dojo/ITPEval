(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_tail_Why3_ide_VClist_tail_loop_inv_3_preserved_goal6:
  preservation of the linked-list segment invariant after advancing one node
  during list-tail traversal. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_tail_Why3_ide_VClist_tail_loop_inv_3_preserved_goal6 =
  ``let lt_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lt_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lt_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lt_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lt_p_linked_n =
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
            mptr (lt_shift array (index + k)) = roots k /\
            lt_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lt_shift (roots k) 0)
    in
      !t_1 : (int # int) -> (int # int).
      !a : int # int.
      !i_1 i_2 : int.
      !a_1 : int # int.
      !i : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_2 = t_1 a in
        let x = i_1 + i_2 in
        let a_3 = t_1 (lt_shift a_1 x) in
        let a_4 = t_1 (lt_shift a_3 0) in
        let x_1 = 1 + i_2 in
          ~(a_2 = (0, 0)) ==>
          ~(a_4 = (0, 0)) ==>
          0 <= i_2 ==>
          i_2 < i ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          lt_framed region t_1 ==>
          linked t ==>
          lt_is_sint32 i ==>
          lt_is_sint32 i_1 ==>
          lt_is_sint32 i_2 ==>
          lt_valid_rw t a 1 ==>
          lt_is_sint32 x_1 ==>
          lt_valid_rw t (lt_shift a_1 0) 2147483646 ==>
          lt_p_linked_n t t_1 a_2 a_1 i_1 i (0, 0) ==>
          lt_p_linked_n t t_1 a_2 a_1 i_1 i_2 a_3 ==>
          lt_p_linked_n t t_1 a_3 a_1 x (i - i_2) (0, 0) ==>
          lt_p_linked_n t t_1 a_2 a_1 i_1 x_1 a_4``;
