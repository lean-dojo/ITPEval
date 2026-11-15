(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19:
  a strncpy not-exceed postcondition verification condition concluding that
  the updated destination is a valid bounded string, under the stated havoc,
  address-order, memory-validity, string-validity, length, and prefix-copy
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal19 =
  ``let sn_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sn_separated =
      \p : int # int. \n : int.
       \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        ~(FST p = FST q) \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let sn_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sn_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sn_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sn_is_sint64 =
      \z : int.
        -9223372036854775808 <= z /\ z < 9223372036854775808
    in
    let sn_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sn_shift s n) = 0 /\
          sn_is_uint64 n /\
          sn_valid_rw malloc (sn_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sn_is_sint8 (mchar (sn_shift s j)))
    in
    let sn_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        sn_valid_rw malloc (sn_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (sn_shift s n) = 0 /\
            n < cnt /\
            sn_is_uint64 n /\
            sn_valid_rw malloc (sn_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           sn_is_sint8 (mchar (sn_shift s j))))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 to_sint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
      !havoc :
        ((int # int) -> int) ->
        ((int # int) -> int) ->
        (int # int) -> int -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          sn_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sn_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          sn_is_sint64 (to_sint64 z)) ==>
        (!z : int.
          sn_is_sint64 z ==>
          to_sint64 z = z) ==>
        (!z : int.
          to_uint64 (to_uint64 z) = to_uint64 z) ==>
        (!z : int.
          to_sint64 (to_uint64 z) = to_sint64 z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sn_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sn_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sn_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (sn_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (sn_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          sn_is_uint64 (l_strnlen mchar s cnt)) ==>
        (!m0 m1 : (int # int) -> int.
         !p : int # int.
         !n : int.
         !q : int # int.
          havoc m0 m1 p n q =
          (if sn_separated q 1 p n then m1 q else m0 q)) ==>
        !a_3 a_1 a : int # int.
        !t_1 t_2 t_3 : (int # int) -> int.
        !t : int -> int.
        !a_2 : int # int.
          let x = FST a_3 in
          let x_1 = FST a_1 in
          let a_4 = sn_shift a_1 0 in
          let x_2 = SND a_1 in
          let x_3 = SND a in
          let x_4 = x_3 - x_2 in
            x <> x_1 ==>
            havoc t_1 t_2 a_4
              (1 + l_strnlen t_3 a_3 0) = t_3 ==>
            x_2 <= x_3 ==>
            region x_1 <= 0 ==>
            region x <= 0 ==>
            x_3 < x_2 + l_strlen t_2 a_3 ==>
            linked t ==>
            sconst t_2 ==>
            addr_le a_1 a ==>
            addr_le a_3 a_2 ==>
            sn_p_valid_str t t_2 a_3 ==>
            sn_p_valid_str t t_3 a_2 ==>
            sn_is_uint64 x_4 ==>
            sn_p_valid_strn t t_2 a_3 x_4 ==>
            sn_p_valid_strn t t_3 a x_4 ==>
            addr_le a (sn_shift a_1 x_4) ==>
            addr_le a_2
              (sn_shift a_3 (l_strnlen t_3 a_3 x_4)) ==>
            sn_valid_rw t a_4
              (1 + l_strnlen t_2 a_3 x_4) ==>
            (!i : int.
              0 <= i ==>
              i + SND a_3 < SND a_2 ==>
              t_3 (sn_shift a_3 i) =
              t_3 (sn_shift a_1 i)) ==>
            sn_p_valid_strn t t_3 a_1 x_4``;
