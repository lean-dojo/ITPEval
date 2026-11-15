(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part2_goal62:
  preservation of the left-swipe relation on an array of list pointers after
  removing the selected item by a functional memory update, under linked-list,
  integer-bound, memory-validity, separation, framing, and uniqueness
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part2_goal62 =
  ``let lr62_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lr62_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lr62_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lr62_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lr62_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lr62_p_linked_n =
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
            mptr (lr62_shift array (index + k)) = roots k /\
            lr62_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lr62_shift (roots k) 0)
    in
    let lr62_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lr62_havoc =
      \old_memory : (int # int) -> (int # int).
       \outside_memory : (int # int) -> (int # int).
       \p : int # int. \n : int. \q : int # int.
        if lr62_separated q 1 p n
        then outside_memory q
        else old_memory q
    in
    let lr62_p_array_swipe_left =
      \mptr0 : (int # int) -> (int # int).
       \mptr1 : (int # int) -> (int # int).
       \array : int # int. \down : int. \up : int.
        !j : int.
          down <= j ==> j < up ==>
          mptr1 (lr62_shift array (1 + j)) =
            mptr0 (lr62_shift array j)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_1 t_2 t_3 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_2 i i_1 : int.
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
           mptr (lr62_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lr62_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_2 = t_1 a in
        let a_3 = t_1 (lr62_shift a_1 i_2) in
        let x = i + i_1 in
        let a_4 = lr62_shift a_1 0 in
        let x_1 = l_index_of t_1 a_3 a_1 i_1 x in
          ~(a_2 = (0, 0)) ==>
          ~(a_3 = (0, 0)) ==>
          a_3 = a_2 ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_1 <= i_2 ==>
          i_2 < x ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          i <= 2147483645 ==>
          lr62_framed region t_1 ==>
          linked t ==>
          lr62_is_sint32 i ==>
          lr62_is_sint32 i_1 ==>
          lr62_valid_rw t a 1 ==>
          lr62_valid_rw t a_4 2147483646 ==>
          lr62_separated a 1 a_4 2147483646 ==>
          lr62_separated a_2 4 a_4 2147483646 ==>
          lr62_p_linked_n t t_1 a_2 a_1 i_1 i (0, 0) ==>
          lr62_is_sint32 x_1 ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x ==>
            lr62_separated a 1
              (t_1 (lr62_shift a_1 i_3)) 4) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x ==>
            lr62_separated
              (t_1 (lr62_shift a_1 i_3)) 4
              a_4 2147483646) ==>
          (!i_3 : int.
            let a_5 = t_1 (lr62_shift a_1 i_3) in
              ~(a_3 = a_5) ==>
              i_1 <= i_3 ==>
              i_3 < x ==>
              lr62_separated a_3 4 a_5 4) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x ==>
            i_4 < x ==>
            ~(t_1 (lr62_shift a_1 i_4) =
              t_1 (lr62_shift a_1 i_3))) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x ==>
            i_4 < x ==>
            lr62_separated
              (t_1 (lr62_shift a_1 i_4)) 4
              (t_1 (lr62_shift a_1 i_3)) 4) ==>
          lr62_havoc t_3 t_1
            (lr62_shift a_1 i_1) (i - 1) = t_2 ==>
          lr62_p_array_swipe_left
            t_2 t_1 a_1 i_1 (i + i_1 - 1) ==>
          lr62_p_array_swipe_left
            (lr62_update t_2 a
              (t_1 (lr62_shift a_2 0)))
            t_1 a_1 x_1 (i + i_1 - 1)``;
