(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_exists_post_goal7:
  a match-string postcondition verification condition identifying the
  recursive search result from pointer-array bounds, string validity, and
  earlier non-match hypotheses. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal7 =
  ``let ms_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ms_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let ms_framed =
      \region : int -> int.
       \mptr : (int # int) -> (int # int).
        !p : int # int. region (FST (mptr p)) <= 0
    in
    let ms_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let ms_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let ms_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ms_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let ms_is_sint64 =
      \z : int.
        -9223372036854775808 <= z /\ z < 9223372036854775808
    in
    let ms_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (ms_shift s n) = 0 /\
          ms_is_uint64 n /\
          ms_valid_rw malloc (ms_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            ms_is_sint8 (mchar (ms_shift s j)))
    in
    let ms_l_cmp =
      \u v : int.
        if v = u then 0 else if u < v then -1 else 1
    in
      !to_uint8 to_sint8 to_uint64 to_sint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strncmp :
        ((int # int) -> int) ->
        (int # int) -> (int # int) -> int -> int.
      !l_real_len :
        ((int # int) -> (int # int)) -> (int # int) -> int -> int.
      !l_match_string :
        ((int # int) -> (int # int)) ->
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int) -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
        (!z : int. ms_is_uint8 (to_uint8 z)) ==>
        (!z : int. ms_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          ms_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          ms_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          to_uint8 (to_uint8 z) = to_uint8 z) ==>
        (!z : int.
          to_sint8 (to_sint8 z) = to_sint8 z) ==>
        (!z : int.
          to_sint8 (to_uint8 z) = to_sint8 z) ==>
        (!z : int. ms_is_uint64 (to_uint64 z)) ==>
        (!z : int. ms_is_sint64 (to_sint64 z)) ==>
        (!z : int.
          ms_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          ms_is_sint64 z ==>
          to_sint64 z = z) ==>
        (!z : int.
          to_uint64 (to_uint64 z) = to_uint64 z) ==>
        (!z : int.
          to_sint64 (to_sint64 z) = to_sint64 z) ==>
        (!z : int.
          to_sint64 (to_uint64 z) = to_sint64 z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (ms_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (ms_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          ms_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !cs ct : int # int.
         !n : int.
          (if n = -1 then
             l_strncmp mchar cs ct n = 0
           else if mchar (ms_shift ct 0) = mchar (ms_shift cs 0) then
             l_strncmp
               mchar (ms_shift cs 1) (ms_shift ct 1) (n - 1) =
             l_strncmp mchar cs ct n
           else
             ms_l_cmp
               (to_uint8 (mchar (ms_shift cs 0)))
               (to_uint8 (mchar (ms_shift ct 0))) =
             l_strncmp mchar cs ct n)) ==>
        (!mptr : (int # int) -> (int # int).
         !base_addr : int # int.
         !n : int.
          (if n = 0 \/ mptr (ms_shift base_addr 0) = (0, 0) then
             l_real_len mptr base_addr n = 0
           else
             to_uint64
               (1 +
                l_real_len
                  mptr
                  (ms_shift base_addr 1)
                  (to_uint64 (n - 1))) =
             l_real_len mptr base_addr n)) ==>
        (!mptr : (int # int) -> (int # int).
         !base_addr : int # int.
         !n : int.
          ms_is_uint64 (l_real_len mptr base_addr n)) ==>
        (!mptr : (int # int) -> (int # int).
         !mchar : (int # int) -> int.
         !base_addr s : int # int.
         !n : int.
          (if n = 0 then
             l_match_string mptr mchar base_addr n s = 0
           else if
             l_strncmp
               mchar
               (mptr (ms_shift base_addr 0))
               s
               (l_strlen mchar (mptr (ms_shift base_addr 0))) =
             0
           then
             l_match_string mptr mchar base_addr n s = 0
           else
             l_match_string
               mptr
               mchar
               (ms_shift base_addr 1)
               (to_uint64 (n - 1))
               s =
             l_match_string mptr mchar base_addr n s)) ==>
        (!mptr : (int # int) -> (int # int).
         !mchar : (int # int) -> int.
         !base_addr s : int # int.
         !n : int.
          ms_is_uint64
            (l_match_string mptr mchar base_addr n s)) ==>
        !t_2 : (int # int) -> (int # int).
        !a_1 : int # int.
        !i i_1 : int.
        !t_1 : (int # int) -> int.
        !i_3 : int.
        !a : int # int.
        !i_2 : int.
        !t : int -> int.
          let x = l_real_len t_2 a_1 i in
          let a_2 = t_2 (ms_shift a_1 i_1) in
          let a_3 = ms_shift a_1 0 in
            l_strncmp
              t_1
              (t_2 (ms_shift a_1 i_3))
              a
              (l_strlen t_1 (t_2 (ms_shift a_1 i_3))) =
            0 ==>
            0 <= i_2 ==>
            0 <= i_3 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            x <= i ==>
            i_3 < x ==>
            i_2 <= x ==>
            i <= 2147483647 ==>
            ms_framed region t_2 ==>
            linked t ==>
            sconst t_1 ==>
            ms_is_sint32 i_2 ==>
            ms_is_uint64 i ==>
            ms_is_uint64 i_3 ==>
            ms_p_valid_str t t_1 a ==>
            (if to_uint64 i_2 < i then
               if t_2 (ms_shift a_1 i_2) = (0, 0) then
                 i_1 = -22
               else
                 i_2 = i_1 /\
                 l_strncmp
                   t_1 a_2 a (l_strlen t_1 a_2) =
                 0 /\
                 ms_p_valid_str t t_1 a_2 /\
                 (!i_4 : int.
                   t_1 (ms_shift a_2 i_4) =
                     t_1 (ms_shift a i_4) \/
                   i_4 < 0 \/
                   l_strlen t_1 a_2 < i_4)
             else
               i_1 = -22) ==>
            (x = i ==> ms_valid_rw t a_3 i) ==>
            (x < i ==> ms_valid_rw t a_3 (1 + x)) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 < i_2 ==>
              ms_p_valid_str
                t t_1 (t_2 (ms_shift a_1 i_4))) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 < i_2 ==>
              l_strncmp
                t_1
                (t_2 (ms_shift a_1 i_4))
                a
                (l_strlen t_1 (t_2 (ms_shift a_1 i_4))) <>
              0) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 < x ==>
              ms_is_uint64 i_4 ==>
              ms_p_valid_str
                t t_1 (t_2 (ms_shift a_1 i_4))) ==>
            l_match_string t_2 t_1 a_1 x a = i_1``;
