(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_2_part1_goal56:
  separation of two distinct updated list-array entries after modeled
  pointer-memory havoc and updates, under linked-list, memory-safety,
  separation, unchangedness, absence, and uniqueness hypotheses. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_2_part1_goal56 =
  ``let lp56_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lp56_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lp56_havoc =
      \m0 : (int # int) -> (int # int).
       \m1 : (int # int) -> (int # int).
       \p : int # int. \a : int. \q : int # int.
        if lp56_separated q 1 p a then m1 q else m0 q
    in
    let lp56_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lp56_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lp56_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lp56_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lp56_p_linked_n =
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
            mptr (lp56_shift array (index + k)) = roots k /\
            lp56_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lp56_shift (roots k) 0)
    in
    let lp56_load_s1_list =
      \p : int # int.
       \mflt : (int # int) -> real.
       \mptr : (int # int) -> (int # int).
        (mptr (lp56_shift p 0),
         (mflt (lp56_shift p 1),
          (mflt (lp56_shift p 2), mflt (lp56_shift p 3))))
    in
    let lp56_eqs1_list =
      \s s_1 : (int # int) # (real # (real # real)).
        FST s_1 = FST s /\
        FST (SND s_1) = FST (SND s) /\
        FST (SND (SND s_1)) = FST (SND (SND s)) /\
        SND (SND (SND s_1)) = SND (SND (SND s))
    in
    let lp56_p_unchanged =
      \malloc0 : int -> int.
       \mptr0 : (int # int) -> (int # int).
       \mflt0 : (int # int) -> real.
       \malloc1 : int -> int.
       \mptr1 : (int # int) -> (int # int).
       \mflt1 : (int # int) -> real.
       \array : int # int. \down : int. \up : int.
        !j : int.
          let cell = lp56_shift array j in
          let node0 = mptr0 cell in
          let node1 = mptr1 cell in
            down <= j ==> j < up ==>
            node0 = node1 /\
            lp56_eqs1_list
              (lp56_load_s1_list node1 mflt1 mptr1)
              (lp56_load_s1_list node0 mflt0 mptr0) /\
            (lp56_valid_rw malloc1 node1 4 ==>
             lp56_valid_rw malloc0 node0 4)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !i i_1 : int.
      !t_3 : (int # int) -> (int # int).
      !a_3 a_4 a_2 : int # int.
      !t_2 : (int # int) -> (int # int).
      !t_4 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !i_3 i_2 : int.
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
           mptr (lp56_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lp56_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let x = i - 1 in
        let x_1 = i + i_1 - 1 in
        let x_2 = l_index_of t_3 a_3 a_4 x x_1 in
        let x_3 = 1 + x_2 in
        let x_4 = i + i_1 in
        let a_5 = lp56_shift a_4 0 in
        let a_6 = t_3 a_2 in
        let a_7 = lp56_shift a_4 x in
        let a_8 =
          lp56_havoc t_2
            (lp56_update
              (lp56_update t_3 a_2 a)
              (lp56_shift
                (t_3 (lp56_shift a_4 (x_2 - 1))) 0)
              a_1)
            (lp56_shift a_4 x_2) (i + i_1 - 1 - x_2)
        in
        let a_9 = a_8 a_2 in
        let a_13 =
          lp56_havoc t_4 a_8 (lp56_shift a_4 x) (1 + i_1)
        in
        let a_10 =
          lp56_update
            (lp56_update a_13 (lp56_shift a_3 0) a_9)
            a_7 a_3
        in
        let a_11 = lp56_update a_10 a_2 a_3 in
          ~(i_3 = i_2) ==>
          ~((0, 0) = a_3) ==>
          x_3 = x_4 ==>
          0 < i ==>
          0 <= i_1 ==>
          i_2 < x_4 ==>
          i_3 < x_4 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          x_2 < x_4 ==>
          i_1 <= 2147483645 ==>
          x_4 <= 2147483646 ==>
          i <= 1 + i_2 ==>
          i <= 1 + i_3 ==>
          i <= x_3 ==>
          lp56_framed region t_3 ==>
          linked t ==>
          lp56_is_sint32 i ==>
          lp56_is_sint32 i_1 ==>
          lp56_valid_rw t a_2 1 ==>
          lp56_valid_rw t a_3 4 ==>
          lp56_separated a_2 1 a_3 4 ==>
          lp56_is_sint32 x ==>
          lp56_valid_rw t a_5 2147483646 ==>
          lp56_separated a_2 1 a_5 2147483646 ==>
          lp56_separated a_3 4 a_5 2147483646 ==>
          lp56_separated a_6 4 a_5 2147483646 ==>
          lp56_valid_rw t a_7 i_1 ==>
          lp56_p_linked_n t t_3 a_6 a_4 x i_1 (0, 0) ==>
          lp56_is_sint32 x_2 ==>
          lp56_separated a_9 4 a_5 2147483646 ==>
          lp56_eqs1_list
            (lp56_load_s1_list a_3 t_1 a_8)
            (lp56_load_s1_list a_3 t_1 t_3) ==>
          lp56_p_linked_n t a_8 a_9 a_4 x i_1 (0, 0) ==>
          lp56_p_unchanged
            t a_8 t_1 t t_3 t_1 a_4 x x_1 ==>
          lp56_p_unchanged
            t a_11 t_1 t a_10 t_1 a_4 x x_4 ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            ~(t_3 (lp56_shift a_4 j) = a_3)) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_is_sint32 j ==>
            ~(t_3 (lp56_shift a_4 j) = a_3)) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_separated a_2 1
              (t_3 (lp56_shift a_4 j)) 4) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_separated
              (t_3 (lp56_shift a_4 j)) 4
              a_5 2147483646) ==>
          (!j : int.
            let a_12 = t_3 (lp56_shift a_4 j) in
              ~(a_12 = a_3) ==>
              i <= 1 + j ==>
              2 + j <= x_4 ==>
              lp56_separated a_3 4 a_12 4) ==>
          (!j_3 j_2 : int.
            ~(j_3 = j_2) ==>
            i <= 1 + j_2 ==>
            i <= 1 + j_3 ==>
            2 + j_2 <= x_4 ==>
            2 + j_3 <= x_4 ==>
            ~(t_3 (lp56_shift a_4 j_3) =
              t_3 (lp56_shift a_4 j_2))) ==>
          (!j_3 j_2 : int.
            ~(j_3 = j_2) ==>
            i <= 1 + j_2 ==>
            i <= 1 + j_3 ==>
            2 + j_2 <= x_4 ==>
            2 + j_3 <= x_4 ==>
            lp56_separated
              (t_3 (lp56_shift a_4 j_3)) 4
              (t_3 (lp56_shift a_4 j_2)) 4) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            ~(a_8 (lp56_shift a_4 j) = a_3)) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_separated a_2 1
              (a_8 (lp56_shift a_4 j)) 4) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_separated a_3 4
              (a_8 (lp56_shift a_4 j)) 4) ==>
          (!j : int.
            i <= 1 + j ==> 2 + j <= x_4 ==>
            lp56_separated
              (a_8 (lp56_shift a_4 j)) 4
              a_5 2147483646) ==>
          (!j_3 j_2 : int.
            ~(j_3 = j_2) ==>
            i <= 1 + j_2 ==>
            i <= 1 + j_3 ==>
            2 + j_2 <= x_4 ==>
            2 + j_3 <= x_4 ==>
            ~(a_8 (lp56_shift a_4 j_3) =
              a_8 (lp56_shift a_4 j_2))) ==>
          (!j_3 j_2 : int.
            ~(j_3 = j_2) ==>
            i <= 1 + j_2 ==>
            i <= 1 + j_3 ==>
            2 + j_2 <= x_4 ==>
            2 + j_3 <= x_4 ==>
            lp56_separated
              (a_8 (lp56_shift a_4 j_3)) 4
              (a_8 (lp56_shift a_4 j_2)) 4) ==>
          a_13 a_2 = a_9 ==>
          lp56_separated
            (a_13 a_2) 4 a_5 2147483646 ==>
          (!j : int.
            i <= j ==> j < x_4 ==>
            lp56_separated a_2 1
              (a_13 (lp56_shift a_4 j)) 4) ==>
          (!j : int.
            i <= j ==> j < x_4 ==>
            lp56_separated
              (a_13 (lp56_shift a_4 j)) 4
              a_5 2147483646) ==>
          (!k j : int.
            ~(k = j) ==>
            i <= j ==> i <= k ==>
            j < x_4 ==> k < x_4 ==>
            lp56_separated
              (a_13 (lp56_shift a_4 k)) 4
              (a_13 (lp56_shift a_4 j)) 4) ==>
          (!k j : int.
            ~(k = j) ==>
            x <= j ==> x <= k ==>
            j < x_4 ==> k < x_4 ==>
            ~(a_13 (lp56_shift a_4 k) =
              a_13 (lp56_shift a_4 j))) ==>
          lp56_p_array_swipe_right
            a_13 a_8 a_4 i x_4 ==>
          lp56_p_linked_n
            t a_13 a_9 a_4 i i_1 (0, 0) ==>
          lp56_separated
            (a_11 (lp56_shift a_4 i_3)) 4
            (a_11 (lp56_shift a_4 i_2)) 4``;
