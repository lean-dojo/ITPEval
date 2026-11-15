(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_part02_goal34:
  writable validity of the final list node after pointer-memory updates,
  havoc, and a null-pointer write in list_add. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val list_add_Why3_ide_VClist_add_call_list_final_add_pre_part02_goal34 =
  ``let la_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let la_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let la_havoc =
      \m0 : (int # int) -> (int # int).
       \m1 : (int # int) -> (int # int).
       \p : int # int. \a : int. \q : int # int.
        if la_separated q 1 p a then m1 q else m0 q
    in
    let la_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let la_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let la_framed =
      \region : int -> int. \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let la_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let la_p_linked_n =
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
            mptr (la_shift array (index + k)) = roots k /\
            la_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (la_shift (roots k) 0)
    in
    let la_load_s1_list =
      \p : int # int.
       \mflt : (int # int) -> real.
       \mptr : (int # int) -> (int # int).
        (mptr (la_shift p 0),
         (mflt (la_shift p 1),
          (mflt (la_shift p 2), mflt (la_shift p 3))))
    in
    let la_eqs1_list =
      \s s_1 : (int # int) # (real # (real # real)).
        FST s_1 = FST s /\
        FST (SND s_1) = FST (SND s) /\
        FST (SND (SND s_1)) = FST (SND (SND s)) /\
        SND (SND (SND s_1)) = SND (SND (SND s))
    in
    let la_p_unchanged =
      \malloc0 : int -> int.
       \mptr0 : (int # int) -> (int # int).
       \mflt0 : (int # int) -> real.
       \malloc1 : int -> int.
       \mptr1 : (int # int) -> (int # int).
       \mflt1 : (int # int) -> real.
       \array : int # int. \down : int. \up : int.
        !j : int.
          let cell = la_shift array j in
          let node0 = mptr0 cell in
          let node1 = mptr1 cell in
            down <= j ==> j < up ==>
            node0 = node1 /\
            la_eqs1_list
              (la_load_s1_list node1 mflt1 mptr1)
              (la_load_s1_list node0 mflt0 mptr0) /\
            (la_valid_rw malloc1 node1 4 ==>
             la_valid_rw malloc0 node0 4)
    in
      !l_index_of :
        ((int # int) -> (int # int)) ->
        (int # int) -> (int # int) -> int -> int -> int.
      !i i_1 : int.
      !a_4 : int # int.
      !t_3 : (int # int) -> (int # int).
      !a_2 a a_1 : int # int.
      !t_2 : (int # int) -> (int # int).
      !a_3 : int # int.
      !t : int -> int.
      !t_1 : (int # int) -> real.
      !region : int -> int.
      !linked : (int -> int) -> bool.
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
           mptr (la_shift array down) = item ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array down up = down) ==>
        (!mptr : (int # int) -> (int # int).
         !array : int # int.
         !down : int.
         !item : int # int.
         !up : int.
           ~(mptr (la_shift array down) = item) ==>
           0 <= down ==>
           down < up ==>
           l_index_of mptr item array (1 + down) up =
             l_index_of mptr item array down up) ==>
        let x = i + i_1 in
        let x_1 = i + i_1 - 1 in
        let a_5 = la_shift a_4 x_1 in
        let m =
          la_update
            (la_update t_3 a_2 a)
            (la_shift (t_3 a_5) 0) a_1
        in
        let a_6 = la_havoc t_2 m (la_shift a_4 x) 0 in
        let a_7 = la_update a_6 (la_shift a_3 0) (0, 0) in
        let a_8 = a_7 a_2 in
        let a_9 = a_7 a_5 in
        let a_10 = la_shift a_4 0 in
        let a_11 = t_3 a_2 in
        let a_12 = m a_2 in
          ~((0, 0) = a_3) ==>
          x = l_index_of t_3 a_3 a_4 i_1 x ==>
          ~(a_8 = (0, 0)) ==>
          ~(a_9 = (0, 0)) ==>
          0 <= i ==>
          0 <= i_1 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          i <= 2147483645 ==>
          i_1 <= 2147483645 ==>
          x <= 2147483645 ==>
          la_framed region t_3 ==>
          linked t ==>
          la_is_sint32 i ==>
          la_is_sint32 i_1 ==>
          la_valid_rw t a_2 1 ==>
          la_valid_rw t a_3 4 ==>
          la_separated a_2 1 a_3 4 ==>
          la_is_sint32 x ==>
          la_valid_rw t a_10 2147483646 ==>
          la_valid_rw t (la_shift a_4 i_1) i ==>
          la_separated a_2 1 a_10 2147483646 ==>
          la_separated a_3 4 a_10 2147483646 ==>
          la_separated a_11 4 a_10 2147483646 ==>
          la_p_linked_n t t_3 a_11 a_4 i_1 i (0, 0) ==>
          la_separated a_12 4 a_10 2147483646 ==>
          la_eqs1_list
            (la_load_s1_list a_3 t_1 a_6)
            (la_load_s1_list a_3 t_1 t_3) ==>
          la_p_linked_n t a_6 a_12 a_4 i_1 i (0, 0) ==>
          la_p_linked_n t a_7 a_8 a_4 i_1 i (0, 0) ==>
          la_p_linked_n t a_7 a_8 a_4 i_1 (i - 1) a_9 ==>
          la_p_unchanged t a_6 t_1 t t_3 t_1 a_4 i_1 x ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            ~(t_3 (la_shift a_4 i_2) = a_3)) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            la_separated a_2 1 (t_3 (la_shift a_4 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            la_separated (t_3 (la_shift a_4 i_2)) 4
              a_10 2147483646) ==>
          (!i_2 : int.
            let a_13 = t_3 (la_shift a_4 i_2) in
              ~(a_13 = a_3) ==>
              i_1 <= i_2 ==>
              i_2 < x ==>
              la_separated a_3 4 a_13 4) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            ~(t_3 (la_shift a_4 i_3) =
              t_3 (la_shift a_4 i_2))) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            ~(m (la_shift a_4 i_2) = a_3)) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            la_separated (t_3 (la_shift a_4 i_3)) 4
              (t_3 (la_shift a_4 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            la_separated a_2 1 (m (la_shift a_4 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            la_separated a_3 4 (m (la_shift a_4 i_2)) 4) ==>
          (!i_2 : int.
            i_1 <= i_2 ==> i_2 < x ==>
            la_separated (m (la_shift a_4 i_2)) 4
              a_10 2147483646) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            ~(m (la_shift a_4 i_3) =
              m (la_shift a_4 i_2))) ==>
          (!i_3 i_2 : int.
            ~(i_3 = i_2) ==>
            i_1 <= i_2 ==>
            i_1 <= i_3 ==>
            i_2 < x ==>
            i_3 < x ==>
            la_separated (m (la_shift a_4 i_3)) 4
              (m (la_shift a_4 i_2)) 4) ==>
          la_valid_rw t a_9 4``;
