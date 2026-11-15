(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_final_add_Why3_ide_VClist_final_add_post_goal0:
  preservation of a linked-list segment after the final two modeled pointer
  updates used to append a list segment. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_final_add_Why3_ide_VClist_final_add_post_goal0 =
  ``let lfa_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lfa_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lfa_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lfa_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lfa_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lfa_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lfa_p_linked_n =
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
            mptr (lfa_shift array (index + k)) = roots k /\
            lfa_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lfa_shift (roots k) 0)
    in
      !t_1 : (int # int) -> (int # int).
      !a_1 : int # int.
      !i i_1 : int.
      !a_3 a a_2 : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_4 = t_1 (lfa_shift a_1 0) in
        let x = i + i_1 in
        let a_5 = lfa_shift a_3 0 in
        let a_6 = t_1 a in
        let a_7 = lfa_shift a_2 0 in
        let m =
          lfa_update
            (lfa_update t_1 (lfa_shift a_3 x) a_1)
            a_7 a_1
        in
          a_4 = (0, 0) ==>
          0 < x ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          x <= 2147483645 ==>
          lfa_framed region t_1 ==>
          linked t ==>
          lfa_is_sint32 i ==>
          lfa_is_sint32 i_1 ==>
          lfa_valid_rw t a 1 ==>
          lfa_valid_rw t a_1 4 ==>
          lfa_valid_rw t a_2 4 ==>
          lfa_separated a 1 a_1 4 ==>
          lfa_separated a 1 a_2 4 ==>
          lfa_separated a_2 4 a_1 4 ==>
          lfa_valid_rw t a_5 2147483646 ==>
          lfa_separated a 1 a_5 2147483646 ==>
          lfa_separated a_1 4 a_5 2147483646 ==>
          lfa_separated a_6 4 a_5 2147483646 ==>
          lfa_p_linked_n t t_1 a_6 a_3 i_1 (i - 1) a_2 ==>
          lfa_p_linked_n t t_1 a_2 a_3
            (i + i_1 - 1) 1 (t_1 a_7) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            lfa_separated a 1 (t_1 (lfa_shift a_3 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            lfa_separated a_1 4 (t_1 (lfa_shift a_3 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            lfa_separated (t_1 (lfa_shift a_3 i_2)) 4
              a_5 2147483646) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            ~(t_1 (lfa_shift a_3 i_3) =
              t_1 (lfa_shift a_3 i_2))) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            lfa_separated (t_1 (lfa_shift a_3 i_3)) 4
              (t_1 (lfa_shift a_3 i_2)) 4) ==>
          lfa_p_linked_n t m (m a) a_3 i_1 (1 + i) a_4``;
