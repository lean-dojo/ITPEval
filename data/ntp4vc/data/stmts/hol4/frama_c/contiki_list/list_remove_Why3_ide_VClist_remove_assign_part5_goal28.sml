(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_assign_part5_goal28:
  classification of the removed-list pointer location under indexed
  linked-segment, memory-validity, separation, uniqueness, and unchangedness
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val list_remove_Why3_ide_VClist_remove_assign_part5_goal28 =
  ``let lr28_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lr28_included =
      \p : int # int. \a : int. \q : int # int. \b : int.
        0 < a ==>
        0 <= b /\ FST p = FST q /\
        SND q <= SND p /\ SND p + a <= SND q + b
    in
    let lr28_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lr28_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lr28_invalid =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        malloc (FST p) <= SND p \/ SND p + n <= 0
    in
    let lr28_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lr28_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lr28_p_linked_n =
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
            mptr (lr28_shift array (index + k)) = roots k /\
            lr28_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lr28_shift (roots k) 0)
    in
    let lr28_load_s1_list =
      \p : int # int.
       \mflt : (int # int) -> real.
       \mptr : (int # int) -> (int # int).
        (mptr (lr28_shift p 0),
         (mflt (lr28_shift p 1),
          (mflt (lr28_shift p 2), mflt (lr28_shift p 3))))
    in
    let lr28_eqs1_list =
      \s s_1 : (int # int) # (real # (real # real)).
        FST s_1 = FST s /\
        FST (SND s_1) = FST (SND s) /\
        FST (SND (SND s_1)) = FST (SND (SND s)) /\
        SND (SND (SND s_1)) = SND (SND (SND s))
    in
    let lr28_p_unchanged =
      \malloc0 : int -> int.
       \mptr0 : (int # int) -> (int # int).
       \mflt0 : (int # int) -> real.
       \malloc1 : int -> int.
       \mptr1 : (int # int) -> (int # int).
       \mflt1 : (int # int) -> real.
       \array : int # int. \down : int. \up : int.
        !j : int.
          let cell = lr28_shift array j in
          let node0 = mptr0 cell in
          let node1 = mptr1 cell in
            down <= j ==> j < up ==>
            node0 = node1 /\
            lr28_eqs1_list
              (lr28_load_s1_list node1 mflt1 mptr1)
              (lr28_load_s1_list node0 mflt0 mptr0) /\
            (lr28_valid_rw malloc1 node1 4 ==>
             lr28_valid_rw malloc0 node0 4)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_2 : (int # int) -> (int # int).
      !a_1 a : int # int.
      !i i_1 : int.
      !a_2 : int # int.
      !i_2 : int.
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
           mptr (lr28_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lr28_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_3 = t_2 a_1 in
        let a_4 = lr28_shift a 0 in
        let a_5 = t_2 a_4 in
        let x = i + i_1 in
        let a_6 = lr28_shift a_2 0 in
        let x_1 = l_index_of t_2 a_5 a_2 i_1 x in
          ~(a_3 = (0, 0)) ==>
          ~(a_5 = (0, 0)) ==>
          ~(a_5 = a_3) ==>
          0 <= i ==>
          0 <= i_1 ==>
          i_1 <= i_2 ==>
          i_2 <= x ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_5) <= 0 ==>
          i <= 2147483645 ==>
          lr28_framed region t_2 ==>
          linked t ==>
          lr28_is_sint32 i ==>
          lr28_is_sint32 i_1 ==>
          lr28_is_sint32 i_2 ==>
          lr28_valid_rw t a_1 1 ==>
          ~lr28_invalid t a_4 1 ==>
          lr28_valid_rw t a_6 2147483646 ==>
          lr28_separated a_1 1 a_6 2147483646 ==>
          lr28_separated a_3 4 a_6 2147483646 ==>
          lr28_p_linked_n t t_2 a_3 a_2 i_1 i (0, 0) ==>
          lr28_p_unchanged
            t t_2 t_1 t t_2 t_1 a_2 i_1 i_2 ==>
          lr28_is_sint32 x_1 ==>
          lr28_p_linked_n t t_2 a a_2 i_2 1 a_5 ==>
          lr28_p_linked_n
            t t_2 a_3 a_2 i_1 (i_2 - i_1) a ==>
          lr28_p_linked_n
            t t_2 a_5 a_2 (1 + i_2)
              (i + i_1 - 1 - i_2) (0, 0) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 <= i_2 ==>
            ~(t_2 (lr28_shift a_2 i_3) = a_5)) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x ==>
            lr28_separated a_1 1
              (t_2 (lr28_shift a_2 i_3)) 4) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < i_2 ==>
            lr28_separated a_5 4
              (t_2 (lr28_shift a_2 i_3)) 4) ==>
          (!i_3 : int.
            i_1 <= i_3 ==> i_3 < x ==>
            lr28_separated
              (t_2 (lr28_shift a_2 i_3)) 4
              a_6 2147483646) ==>
          (!i_3 : int.
            let a_7 = t_2 (lr28_shift a_2 i_3) in
              ~(a_7 = a_5) ==>
              i_1 <= i_3 ==>
              i_3 < x ==>
              lr28_separated a_5 4 a_7 4) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x ==>
            i_4 < x ==>
            ~(t_2 (lr28_shift a_2 i_4) =
              t_2 (lr28_shift a_2 i_3))) ==>
          (!i_4 i_3 : int.
            ~(i_4 = i_3) ==>
            i_1 <= i_3 ==>
            i_1 <= i_4 ==>
            i_3 < x ==>
            i_4 < x ==>
            lr28_separated
              (t_2 (lr28_shift a_2 i_4)) 4
              (t_2 (lr28_shift a_2 i_3)) 4) ==>
          a_4 = a_1 \/
          lr28_shift
            (t_2 (lr28_shift a_2 (x_1 - 1))) 0 = a_4 \/
          lr28_included a_4 1
            (lr28_shift a_2 x_1) (i + i_1 - x_1)``;
