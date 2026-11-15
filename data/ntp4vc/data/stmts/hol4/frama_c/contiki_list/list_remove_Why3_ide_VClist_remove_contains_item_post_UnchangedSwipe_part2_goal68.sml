(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part2_goal68:
  equality of list-node records loaded from adjacent pointer-array entries
  after a single pointer-memory update, under integer-bound, memory-validity,
  framing, linked-segment, separation, index-of, and pointer-uniqueness
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part2_goal68 =
  ``let lr68_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lr68_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lr68_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lr68_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lr68_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lr68_p_linked_n =
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
            mptr (lr68_shift array (index + k)) = roots k /\
            lr68_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lr68_shift (roots k) 0)
    in
    let lr68_load_s1_list =
      \p : int # int.
       \mflt : (int # int) -> real.
       \mptr : (int # int) -> (int # int).
        (mptr (lr68_shift p 0),
         (mflt (lr68_shift p 1),
          (mflt (lr68_shift p 2), mflt (lr68_shift p 3))))
    in
    let lr68_eqs1_list =
      \s s_1 : (int # int) # (real # (real # real)).
        FST s_1 = FST s /\
        FST (SND s_1) = FST (SND s) /\
        FST (SND (SND s_1)) = FST (SND (SND s)) /\
        SND (SND (SND s_1)) = SND (SND (SND s))
    in
    let lr68_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lr68_havoc =
      \old_memory : (int # int) -> (int # int).
       \outside_memory : (int # int) -> (int # int).
       \p : int # int. \n : int. \q : int # int.
        if lr68_separated q 1 p n
        then outside_memory q
        else old_memory q
    in
    let lr68_p_array_swipe_left =
      \mptr0 : (int # int) -> (int # int).
       \mptr1 : (int # int) -> (int # int).
       \array : int # int. \down : int. \up : int.
        !j : int.
          down <= j ==> j < up ==>
          mptr1 (lr68_shift array (1 + j)) =
            mptr0 (lr68_shift array j)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_2 t_3 t_4 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_2 i i_1 i_3 : int.
      !t : int -> int.
      !t_1 : (int # int) -> real.
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
           mptr (lr68_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lr68_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_2 = t_2 a in
        let a_3 = t_2 (lr68_shift a_1 i_2) in
        let x = i + i_1 in
        let x_1 = l_index_of t_2 a_3 a_1 i_1 x in
        let a_4 = lr68_shift a_1 0 in
        let m = lr68_update t_3 a
          (t_2 (lr68_shift a_2 0)) in
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
          x_1 <= i_3 ==>
          i <= 2147483645 ==>
          2 + i_3 <= x ==>
          lr68_framed region t_2 ==>
          linked t ==>
          lr68_is_sint32 i ==>
          lr68_is_sint32 i_1 ==>
          lr68_valid_rw t a 1 ==>
          lr68_valid_rw t a_4 2147483646 ==>
          lr68_separated a 1 a_4 2147483646 ==>
          lr68_separated a_2 4 a_4 2147483646 ==>
          lr68_p_linked_n
            t t_2 a_2 a_1 i_1 i (0, 0) ==>
          lr68_is_sint32 x_1 ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < x ==>
            lr68_separated a 1
              (t_2 (lr68_shift a_1 i_4)) 4) ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < x ==>
            lr68_separated
              (t_2 (lr68_shift a_1 i_4)) 4
              a_4 2147483646) ==>
          (!i_4 : int.
            let a_5 = t_2 (lr68_shift a_1 i_4) in
              ~(a_3 = a_5) ==>
              i_1 <= i_4 ==>
              i_4 < x ==>
              lr68_separated a_3 4 a_5 4) ==>
          (!i_5 i_4 : int.
            ~(i_5 = i_4) ==>
            i_1 <= i_4 ==>
            i_1 <= i_5 ==>
            i_4 < x ==>
            i_5 < x ==>
            ~(t_2 (lr68_shift a_1 i_5) =
              t_2 (lr68_shift a_1 i_4))) ==>
          (!i_5 i_4 : int.
            ~(i_5 = i_4) ==>
            i_1 <= i_4 ==>
            i_1 <= i_5 ==>
            i_4 < x ==>
            i_5 < x ==>
            lr68_separated
              (t_2 (lr68_shift a_1 i_5)) 4
              (t_2 (lr68_shift a_1 i_4)) 4) ==>
          lr68_havoc t_4 t_2
            (lr68_shift a_1 i_1) (i - 1) = t_3 ==>
          lr68_p_array_swipe_left
            t_3 t_2 a_1 i_1 (i + i_1 - 1) ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < i + i_1 - 1 ==>
            lr68_separated a 1
              (t_3 (lr68_shift a_1 i_4)) 4) ==>
          (!i_4 : int.
            i_1 <= i_4 ==> i_4 < i + i_1 - 1 ==>
            lr68_separated
              (t_3 (lr68_shift a_1 i_4)) 4
              a_4 2147483646) ==>
          lr68_eqs1_list
            (lr68_load_s1_list
              (m (lr68_shift a_1 i_3)) t_1 m)
            (lr68_load_s1_list
              (t_2 (lr68_shift a_1 (1 + i_3))) t_1 t_2)``;
