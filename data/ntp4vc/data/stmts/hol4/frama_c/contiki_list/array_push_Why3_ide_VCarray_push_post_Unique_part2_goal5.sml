(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_list/array_push_Why3_ide_VCarray_push_post_Unique_part2_goal5:
  uniqueness of two distinct indexed array-push list nodes after the modeled
  pointer-memory havoc and null-pointer update. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val array_push_Why3_ide_VCarray_push_post_Unique_part2_goal5 =
  ``let ap_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ap_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let ap_havoc =
      \m0 : (int # int) -> (int # int).
       \m1 : (int # int) -> (int # int).
       \p : int # int. \a : int. \q : int # int.
        if ap_separated q 1 p a then m1 q else m0 q
    in
    let ap_update =
      \f : (int # int) -> (int # int).
       \p : int # int. \v : int # int. \q : int # int.
        if q = p then v else f q
    in
    let ap_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ap_framed =
      \region : int -> int. \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ap_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ap_p_linked_n =
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
            mptr (ap_shift array (index + k)) = roots k /\
            ap_valid_rw malloc (roots k) 4 /\
            roots (k + 1) = mptr (ap_shift (roots k) 0)
    in
    let ap_p_array_swipe_right =
      \mptr0 : (int # int) -> (int # int).
       \mptr1 : (int # int) -> (int # int).
       \array : int # int. \down : int. \up : int.
        !j : int.
          down <= j ==> j < up ==>
          mptr1 (ap_shift array (j - 1)) = mptr0 (ap_shift array j)
    in
    let ap_p_unchanged =
      \malloc0 : int -> int.
       \mptr0 : (int # int) -> (int # int).
       \mflt0 : (int # int) -> real.
       \malloc1 : int -> int.
       \mptr1 : (int # int) -> (int # int).
       \mflt1 : (int # int) -> real.
       \array : int # int. \down : int. \up : int.
        !j : int.
          let cell = ap_shift array j in
          let node0 = mptr0 cell in
          let node1 = mptr1 cell in
            down <= j ==> j < up ==>
            node0 = node1 /\
            mptr0 (ap_shift node0 0) = mptr1 (ap_shift node1 0) /\
            mflt0 (ap_shift node0 1) = mflt1 (ap_shift node1 1) /\
            mflt0 (ap_shift node0 2) = mflt1 (ap_shift node1 2) /\
            mflt0 (ap_shift node0 3) = mflt1 (ap_shift node1 3) /\
            (ap_valid_rw malloc1 node1 4 ==>
             ap_valid_rw malloc0 node0 4)
    in
      !i_1 i_2 : int.
      !t_2 t_3 : (int # int) -> (int # int).
      !a_4 a_1 : int # int.
      !i_3 i_5 i_4 i : int.
      !a a_3 : int # int.
      !t : int -> int.
      !a_2 : int # int.
      !t_1 : (int # int) -> real.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let x = i_1 + i_2 in
        let a_5 =
          ap_havoc t_2 t_3 (ap_shift a_4 (1 + i_2)) i_1
        in
        let a_6 = t_3 a_1 in
        let a_7 = ap_shift a_4 0 in
        let x_1 = 1 + i_3 in
        let a_8 =
          ap_update
            (ap_havoc t_2 t_3 (ap_shift a_4 x_1) i_1)
            (ap_shift a_4 i_3) (0, 0)
        in
          ~(i_1 = 0) ==>
          ~(i_5 = i_4) ==>
          (x = i_3 <=> i = 0) ==>
          (i_3 < x <=> i = 1) ==>
          a_5 a_1 = a_6 ==>
          i_3 <= i_2 ==>
          i_2 <= i_3 ==>
          i_2 <= i_4 ==>
          i_2 <= i_5 ==>
          i_3 <= x ==>
          i_4 <= x ==>
          i_5 <= x ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          x <= 2147483645 ==>
          ap_framed region t_3 ==>
          linked t ==>
          ap_is_sint32 i ==>
          ap_is_sint32 i_1 ==>
          ap_is_sint32 i_2 ==>
          ap_is_sint32 i_3 ==>
          ap_valid_rw t a_1 1 ==>
          ap_is_sint32 x ==>
          ap_valid_rw t a_7 2147483646 ==>
          ap_separated a_1 1 a_7 2147483646 ==>
          ap_separated a_6 4 a_7 2147483646 ==>
          ap_p_linked_n t t_3 a a_4 i_2 i_1 a_3 ==>
          ap_p_array_swipe_right a_5 t_3 a_4 x_1
            (1 + i_1 + i_2) ==>
          ap_p_linked_n t a_5 a a_4 i_2 (i_3 - i_2) a_2 ==>
          ap_p_linked_n t a_5 a_2 a_4 x_1
            (i_1 + i_2 - i_3) a_3 ==>
          ap_p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_2 i_3 ==>
          (!i_6 : int.
            i_2 <= i_6 ==> i_6 < x ==>
            ap_separated a_1 1 (t_3 (ap_shift a_4 i_6)) 4) ==>
          (!i_6 : int.
            i_2 <= i_6 ==> i_6 < x ==>
            ap_separated (t_3 (ap_shift a_4 i_6)) 4
              a_7 2147483646) ==>
          (!i_7 i_6 : int.
            ~(i_7 = i_6) ==>
            i_2 <= i_6 ==>
            i_2 <= i_7 ==>
            i_6 < x ==>
            i_7 < x ==>
            ~(t_3 (ap_shift a_4 i_7) =
              t_3 (ap_shift a_4 i_6))) ==>
          (!i_7 i_6 : int.
            ~(i_7 = i_6) ==>
            i_2 <= i_6 ==>
            i_2 <= i_7 ==>
            i_6 < x ==>
            i_7 < x ==>
            ap_separated (t_3 (ap_shift a_4 i_7)) 4
              (t_3 (ap_shift a_4 i_6)) 4) ==>
          (!i_6 : int.
            i_3 < i_6 ==> i_6 <= x ==>
            ap_separated a_1 1 (a_5 (ap_shift a_4 i_6)) 4) ==>
          (!i_6 : int.
            i_2 <= i_6 ==> i_6 < i + i_1 + i_2 ==>
            ap_separated (a_5 (ap_shift a_4 i_6)) 4
              a_7 2147483646) ==>
          ~(a_8 (ap_shift a_4 i_5) =
            a_8 (ap_shift a_4 i_4))``;
