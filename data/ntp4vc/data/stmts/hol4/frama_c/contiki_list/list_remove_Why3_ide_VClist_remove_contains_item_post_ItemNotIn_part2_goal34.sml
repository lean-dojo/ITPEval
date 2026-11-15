(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_ItemNotIn_part2_goal34:
  non-membership of the removed item after a pointer-memory update, under
  linked-segment, integer-bound, memory-validity, separation, and uniqueness
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_remove_Why3_ide_VClist_remove_contains_item_post_ItemNotIn_part2_goal34 =
  ``let lr34_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lr34_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lr34_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lr34_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lr34_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lr34_p_linked_n =
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
            mptr (lr34_shift array (index + k)) = roots k /\
            lr34_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lr34_shift (roots k) 0)
    in
    let lr34_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_1 : (int # int) -> (int # int).
      !t_2 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_2 i i_1 i_3 : int.
      !t : int -> int.
        (!up down : int.
         !mptr : (int # int) -> (int # int).
         !item array : int # int.
           up <= down ==>
           0 <= up ==>
           l_index_of mptr item array down up = up) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           mptr (lr34_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lr34_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_2 = t_1 a in
        let a_3 = t_1 (lr34_shift a_1 i_2) in
        let x = i + i_1 in
        let a_4 = lr34_shift a_1 0 in
          ~(a_2 = (0, 0)) ==>
          ~(a_3 = (0, 0)) ==>
          a_3 = a_2 ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_1 <= i_2 ==>
          i_1 <= i_3 ==>
          i_2 < x ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          i <= 2147483645 ==>
          2 + i_3 <= x ==>
          lr34_framed region t_1 ==>
          linked t ==>
          lr34_is_sint32 i ==>
          lr34_is_sint32 i_1 ==>
          lr34_valid_rw t a 1 ==>
          lr34_valid_rw t a_4 2147483646 ==>
          lr34_separated a 1 a_4 2147483646 ==>
          lr34_separated a_2 4 a_4 2147483646 ==>
          lr34_p_linked_n t t_1 a_2 a_1 i_1 i (0, 0) ==>
          lr34_is_sint32
            (l_index_of t_1 a_3 a_1 i_1 x) ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < x ==>
            lr34_separated a 1
              (t_1 (lr34_shift a_1 i_4)) 4) ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < x ==>
            lr34_separated
              (t_1 (lr34_shift a_1 i_4)) 4
              a_4 2147483646) ==>
          (!i_4 : int.
            let a_5 = t_1 (lr34_shift a_1 i_4) in
              ~(a_3 = a_5) ==>
              i_1 <= i_4 ==>
              i_4 < x ==>
              lr34_separated a_3 4 a_5 4) ==>
          (!i_5 i_4 : int.
            ~(i_5 = i_4) ==>
            i_1 <= i_4 ==>
            i_1 <= i_5 ==>
            i_4 < x ==>
            i_5 < x ==>
            ~(t_1 (lr34_shift a_1 i_5) =
              t_1 (lr34_shift a_1 i_4))) ==>
          (!i_5 i_4 : int.
            ~(i_5 = i_4) ==>
            i_1 <= i_4 ==>
            i_1 <= i_5 ==>
            i_4 < x ==>
            i_5 < x ==>
            lr34_separated
              (t_1 (lr34_shift a_1 i_5)) 4
              (t_1 (lr34_shift a_1 i_4)) 4) ==>
          (!i_4 : int.
            i_1 <= i_4 ==>
            i_4 < i_1 + i - 1 ==>
            ~(t_2 (lr34_shift a_1 i_4) = a_3)) ==>
          ~(lr34_update t_2 a
              (t_1 (lr34_shift a_2 0))
              (lr34_shift a_1 i_3) = a_3)``;
