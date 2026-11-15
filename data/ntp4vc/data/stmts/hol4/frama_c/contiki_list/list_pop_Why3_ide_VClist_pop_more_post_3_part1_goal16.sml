(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_3_part1_goal16:
  preservation of the indexed linked-list predicate after a pointer-memory
  update in list_pop, under validity, framing, and separation assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_pop_Why3_ide_VClist_pop_more_post_3_part1_goal16 =
  ``let lp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lp_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lp_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lp_framed =
      \region : int -> int. \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lp_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lp_p_linked_n =
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
            mptr (lp_shift array (index + k)) = roots k /\
            lp_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lp_shift (roots k) 0)
    in
      !t_1 t_2 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i i_1 : int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_2 = t_1 a in
        let a_3 = lp_shift a_1 0 in
        let x = i + i_1 in
        let a_4 = t_1 (lp_shift a_2 0) in
          ~(a_2 = (0, 0)) ==>
          0 < i ==>
          0 <= i_1 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          lp_framed region t_1 ==>
          linked t ==>
          lp_is_sint32 i ==>
          lp_is_sint32 i_1 ==>
          lp_valid_rw t a 1 ==>
          lp_valid_rw t a_3 2147483646 ==>
          lp_separated a 1 a_3 2147483646 ==>
          lp_separated a_2 4 a_3 2147483646 ==>
          lp_p_linked_n t t_1 a_2 a_1 i_1 i (0, 0) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            lp_separated a 1 (t_1 (lp_shift a_1 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            lp_separated (t_1 (lp_shift a_1 i_2)) 4
              a_3 2147483646) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            ~(t_1 (lp_shift a_1 i_3) =
              t_1 (lp_shift a_1 i_2))) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            lp_separated (t_1 (lp_shift a_1 i_3)) 4
              (t_1 (lp_shift a_1 i_2)) 4) ==>
          lp_p_linked_n t t_2 a_4 a_1 i_1 (i - 1) (0, 0) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < i_1 + (i - 1) ==>
            lp_separated a 1 (t_2 (lp_shift a_1 i_2)) 4) ==>
          lp_p_linked_n t (lp_update t_2 a a_4)
            a_4 a_1 i_1 (i - 1) (0, 0)``;
