(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_part4_goal29:
  preservation of the linked-list segment after modeled pointer-memory havoc
  and updates, under memory-safety, separation, unchangedness, array-swipe,
  occurrence, and uniqueness hypotheses. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val list_push_Why3_ide_VClist_push_contains_item_post_part4_goal29 =
  ``let lp29_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let lp29_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let lp29_havoc =
      \m0 : (int # int) -> (int # int).
       \m1 : (int # int) -> (int # int).
       \p : int # int. \a : int. \q : int # int.
        if lp29_separated q 1 p a then m1 q else m0 q
    in
    let lp29_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let lp29_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let lp29_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let lp29_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let lp29_p_linked_n =
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
            mptr (lp29_shift array (index + k)) = roots k /\
            lp29_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (lp29_shift (roots k) 0)
    in
    let lp29_load_s1_list =
      \p : int # int.
       \mflt : (int # int) -> real.
       \mptr : (int # int) -> (int # int).
        (mptr (lp29_shift p 0),
         (mflt (lp29_shift p 1),
          (mflt (lp29_shift p 2), mflt (lp29_shift p 3))))
    in
    let lp29_eqs1_list =
      \s s_1 : (int # int) # (real # (real # real)).
        FST s_1 = FST s /\
        FST (SND s_1) = FST (SND s) /\
        FST (SND (SND s_1)) = FST (SND (SND s)) /\
        SND (SND (SND s_1)) = SND (SND (SND s))
    in
    let lp29_p_unchanged =
      \malloc0 : int -> int.
       \mptr0 : (int # int) -> (int # int).
       \mflt0 : (int # int) -> real.
       \malloc1 : int -> int.
       \mptr1 : (int # int) -> (int # int).
       \mflt1 : (int # int) -> real.
       \array : int # int. \down : int. \up : int.
        !j : int.
          let cell = lp29_shift array j in
          let node0 = mptr0 cell in
          let node1 = mptr1 cell in
            down <= j ==> j < up ==>
            node0 = node1 /\
            lp29_eqs1_list
              (lp29_load_s1_list node1 mflt1 mptr1)
              (lp29_load_s1_list node0 mflt0 mptr0) /\
            (lp29_valid_rw malloc1 node1 4 ==>
             lp29_valid_rw malloc0 node0 4)
    in
    let lp29_p_array_swipe_left =
      \mptr0 : (int # int) -> (int # int).
       \mptr1 : (int # int) -> (int # int).
       \array : int # int. \down : int. \up : int.
        !j : int.
          down <= j ==> j < up ==>
          mptr1 (lp29_shift array (1 + j)) =
            mptr0 (lp29_shift array j)
    in
    let lp29_p_array_swipe_right =
      \mptr0 : (int # int) -> (int # int).
       \mptr1 : (int # int) -> (int # int).
       \array : int # int. \down : int. \up : int.
        !j : int.
          down <= j ==> j < up ==>
          mptr1 (lp29_shift array (j - 1)) =
            mptr0 (lp29_shift array j)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !t_3 : (int # int) -> (int # int).
      !a_3 : int # int.
      !i_3 i_2 i_1 i : int.
      !a_2 : int # int.
      !t_2 : (int # int) -> (int # int).
      !a a_1 : int # int.
      !t : int -> int.
      !t_1 : (int # int) -> real.
      !t_4 : (int # int) -> (int # int).
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
           mptr (lp29_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (lp29_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let a_4 = t_3 (lp29_shift a_3 i_3) in
        let a_5 = t_3 (lp29_shift a_3 i_2) in
        let x = i_1 - 1 in
        let x_1 = i + i_1 in
        let x_2 = l_index_of t_3 a_4 a_3 x x_1 in
        let x_3 = 1 + i in
        let a_6 = lp29_shift a_3 0 in
        let a_7 = t_3 a_2 in
        let a_8 = lp29_shift a_3 x in
        let x_4 = x_2 - 1 in
        let a_9 = lp29_shift a_3 x_4 in
        let a_10 = t_3 a_9 in
        let a_11 =
          lp29_havoc t_2
            (lp29_update
              (lp29_update t_3 a_2 a)
              (lp29_shift a_10 0) a_1)
            (lp29_shift a_3 x_2) (i + i_1 - x_2)
        in
        let a_12 = a_11 a_2 in
        let a_16 =
          lp29_havoc t_4 a_11 (lp29_shift a_3 x) x_3
        in
        let a_13 =
          lp29_update
            (lp29_update a_16 (lp29_shift a_4 0) a_12)
            a_8 a_4
        in
        let a_14 = lp29_update a_13 a_2 a_4 in
        let occurs =
          ?j : int.
            a_4 = t_3 (lp29_shift a_3 j) /\
            j < x_1 /\ i_1 <= 1 + j
        in
        let absent =
          !j : int.
            j < x_1 ==> i_1 <= 1 + j ==>
            ~(a_4 = t_3 (lp29_shift a_3 j))
        in
          ~(a_4 = (0, 0)) ==>
          a_4 = a_5 ==>
          x_2 = l_index_of t_3 a_5 a_3 x x_1 ==>
          ~(x_1 = x_2) ==>
          0 < i_1 ==>
          i_2 < x_1 ==>
          i_3 < x_1 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          x_2 < x_1 ==>
          x_2 <= x_1 ==>
          -1 <= i ==>
          i <= 2147483644 ==>
          x_1 <= 2147483645 ==>
          i_1 <= 1 + i_2 ==>
          i_1 <= 1 + i_3 ==>
          i_1 <= 1 + x_2 ==>
          lp29_framed region t_3 ==>
          linked t ==>
          lp29_is_sint32 i ==>
          lp29_is_sint32 i_1 ==>
          lp29_valid_rw t a_2 1 ==>
          lp29_is_sint32 x ==>
          lp29_is_sint32 x_3 ==>
          lp29_valid_rw t a_6 2147483646 ==>
          lp29_valid_rw t a_5 4 ==>
          lp29_separated a_2 1 a_6 2147483646 ==>
          lp29_separated a_7 4 a_6 2147483646 ==>
          lp29_separated a_2 1 a_5 4 ==>
          lp29_separated a_5 4 a_6 2147483646 ==>
          lp29_valid_rw t a_8 x_3 ==>
          lp29_p_linked_n t t_3 a_7 a_3 x x_3 (0, 0) ==>
          lp29_is_sint32 x_2 ==>
          lp29_separated a_12 4 a_6 2147483646 ==>
          lp29_eqs1_list
            (lp29_load_s1_list a_4 t_1 a_11)
            (lp29_load_s1_list a_4 t_1 t_3) ==>
          lp29_p_unchanged
            t a_14 t_1 t a_13 t_1 a_3 x x_1 ==>
          (i_1 <= x_2 ==> occurs ==> a_11 a_9 = a_10) ==>
          (occurs ==>
           lp29_p_array_swipe_left
             a_11 t_3 a_3 x_2 (i + i_1 - 1)) ==>
          (absent ==>
           !j : int.
             j < x_1 ==> i_1 <= 1 + j ==>
             ~(a_11 (lp29_shift a_3 j) = a_4)) ==>
          (occurs ==>
           !j : int.
             i_1 <= 1 + j ==> 2 + j <= x_1 ==>
             ~(a_11 (lp29_shift a_3 j) = a_4)) ==>
          (occurs ==>
           lp29_p_linked_n
             t a_11 a_12 a_3 x i (0, 0)) ==>
          (absent ==>
           lp29_p_linked_n
             t a_11 a_12 a_3 x x_3 (0, 0)) ==>
          (absent ==>
           lp29_p_unchanged
             t a_11 t_1 t t_3 t_1 a_3 x x_1) ==>
          (occurs ==>
           lp29_p_unchanged
             t a_11 t_1 t t_3 t_1 a_3 x x_4) ==>
          (absent ==>
           !j : int.
             j < x_1 ==> i_1 <= 1 + j ==>
             lp29_separated a_2 1
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (occurs ==>
           !j : int.
             i_1 <= 1 + j ==> 2 + j <= x_1 ==>
             lp29_separated a_2 1
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (absent ==>
           !j : int.
             j < x_1 ==> i_1 <= 1 + j ==>
             lp29_separated a_4 4
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (occurs ==>
           !j : int.
             i_1 <= 1 + j ==> 2 + j <= x_1 ==>
             lp29_separated a_4 4
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (absent ==>
           !j : int.
             j < x_1 ==> i_1 <= 1 + j ==>
             lp29_separated
               (a_11 (lp29_shift a_3 j)) 4
               a_6 2147483646) ==>
          (occurs ==>
           !j : int.
             i_1 <= 1 + j ==> 2 + j <= x_1 ==>
             lp29_separated
               (a_11 (lp29_shift a_3 j)) 4
               a_6 2147483646) ==>
          (occurs ==>
           !j : int.
             x_2 <= j ==> 2 + j <= x_1 ==>
             lp29_eqs1_list
               (lp29_load_s1_list
                 (a_11 (lp29_shift a_3 j)) t_1 a_11)
               (lp29_load_s1_list
                 (t_3 (lp29_shift a_3 (1 + j))) t_1 t_3)) ==>
          (absent ==>
           !j_2 j : int.
             ~(j_2 = j) ==>
             j < x_1 ==>
             j_2 < x_1 ==>
             i_1 <= 1 + j ==>
             i_1 <= 1 + j_2 ==>
             ~(a_11 (lp29_shift a_3 j_2) =
               a_11 (lp29_shift a_3 j))) ==>
          (occurs ==>
           !j_2 j : int.
             ~(j_2 = j) ==>
             i_1 <= 1 + j ==>
             i_1 <= 1 + j_2 ==>
             2 + j <= x_1 ==>
             2 + j_2 <= x_1 ==>
             ~(a_11 (lp29_shift a_3 j_2) =
               a_11 (lp29_shift a_3 j))) ==>
          (absent ==>
           !j_2 j : int.
             ~(j_2 = j) ==>
             j < x_1 ==>
             j_2 < x_1 ==>
             i_1 <= 1 + j ==>
             i_1 <= 1 + j_2 ==>
             lp29_separated
               (a_11 (lp29_shift a_3 j_2)) 4
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (occurs ==>
           !j_2 j : int.
             ~(j_2 = j) ==>
             i_1 <= 1 + j ==>
             i_1 <= 1 + j_2 ==>
             2 + j <= x_1 ==>
             2 + j_2 <= x_1 ==>
             lp29_separated
               (a_11 (lp29_shift a_3 j_2)) 4
               (a_11 (lp29_shift a_3 j)) 4) ==>
          (!j : int.
            j < x_1 ==> i_1 <= 1 + j ==>
            lp29_separated a_2 1
              (t_3 (lp29_shift a_3 j)) 4) ==>
          (!j : int.
            j < x_1 ==> i_1 <= 1 + j ==>
            lp29_separated
              (t_3 (lp29_shift a_3 j)) 4
              a_6 2147483646) ==>
          (!j : int.
            let a_15 = t_3 (lp29_shift a_3 j) in
              ~(a_5 = a_15) ==>
              j < x_1 ==>
              i_1 <= 1 + j ==>
              lp29_separated a_5 4 a_15 4) ==>
          (!j : int.
            let a_15 = t_3 (lp29_shift a_3 j) in
              ~(a_4 = a_15) ==>
              j < x_1 ==>
              i_1 <= 1 + j ==>
              lp29_separated a_4 4 a_15 4) ==>
          (!j_2 j : int.
            ~(j_2 = j) ==>
            j < x_1 ==>
            j_2 < x_1 ==>
            i_1 <= 1 + j ==>
            i_1 <= 1 + j_2 ==>
            ~(t_3 (lp29_shift a_3 j_2) =
              t_3 (lp29_shift a_3 j))) ==>
          (!j_2 j : int.
            ~(j_2 = j) ==>
            j < x_1 ==>
            j_2 < x_1 ==>
            i_1 <= 1 + j ==>
            i_1 <= 1 + j_2 ==>
            lp29_separated
              (t_3 (lp29_shift a_3 j_2)) 4
              (t_3 (lp29_shift a_3 j)) 4) ==>
          a_16 a_2 = a_12 ==>
          lp29_separated (a_16 a_2) 4 a_6 2147483646 ==>
          (!j : int.
            i_1 <= j ==> j < x_1 ==>
            lp29_separated a_2 1
              (a_16 (lp29_shift a_3 j)) 4) ==>
          (!j : int.
            i_1 <= j ==> j < x_1 ==>
            lp29_separated
              (a_16 (lp29_shift a_3 j)) 4
              a_6 2147483646) ==>
          (!k j : int.
            ~(k = j) ==>
            i_1 <= j ==> i_1 <= k ==>
            j < x_1 ==> k < x_1 ==>
            lp29_separated
              (a_16 (lp29_shift a_3 k)) 4
              (a_16 (lp29_shift a_3 j)) 4) ==>
          (!k j : int.
            ~(k = j) ==>
            x <= j ==> x <= k ==>
            j < x_1 ==> k < x_1 ==>
            ~(a_16 (lp29_shift a_3 k) =
              a_16 (lp29_shift a_3 j))) ==>
          lp29_p_array_swipe_right
            a_16 a_11 a_3 i_1 x_1 ==>
          lp29_p_linked_n
            t a_16 a_12 a_3 i_1 i (0, 0) ==>
          lp29_p_linked_n t a_14 a_4 a_3 x x_3 (0, 0)``;
