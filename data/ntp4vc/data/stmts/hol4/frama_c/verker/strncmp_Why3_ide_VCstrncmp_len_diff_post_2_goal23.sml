(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23:
  a bounded string-comparison length-difference verification condition
  concluding that the comparison result is one, under the stated memory,
  length, address-order, byte-range, and prefix-equality assumptions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal23 =
  ``let sncmp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sncmp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sncmp_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sncmp_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let sncmp_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sncmp_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sncmp_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sncmp_shift s n) = 0 /\
          sncmp_is_uint64 n /\
          sncmp_valid_rw malloc (sncmp_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sncmp_is_sint8 (mchar (sncmp_shift s j)))
    in
    let sncmp_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        sncmp_valid_rw malloc (sncmp_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (sncmp_shift s n) = 0 /\
            n < cnt /\
            sncmp_is_uint64 n /\
            sncmp_valid_rw malloc (sncmp_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           sncmp_is_sint8 (mchar (sncmp_shift s j))))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint8 to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          sncmp_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          sncmp_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          sncmp_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sncmp_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sncmp_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sncmp_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sncmp_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (sncmp_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (sncmp_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          sncmp_is_uint64 (l_strnlen mchar s cnt)) ==>
        !a_1 a_2 a a_3 : int # int.
        !i_1 : int.
        !t_1 : (int # int) -> int.
        !t : int -> int.
        !i_2 i_3 i : int.
          let x = SND a_1 in
          let x_1 = SND a_2 in
          let x_2 = SND a in
          let x_3 = SND a_3 in
          let x_4 = i_1 + x - x_2 in
          let x_5 = l_strnlen t_1 a_1 i_1 in
          let x_6 = x + x_5 in
          let x_7 = l_strnlen t_1 a_3 i_1 in
          let x_8 = i_1 + x in
            x + x_1 = x_2 + x_3 ==>
            x_2 + l_strnlen t_1 a x_4 = x_6 ==>
            x_1 + l_strnlen t_1 a_2 x_4 = x_3 + x_7 ==>
            0 < i_1 ==>
            x <= x_2 ==>
            region (FST a_1) <= 0 ==>
            region (FST a_3) <= 0 ==>
            x_5 < x_7 ==>
            x_2 <= x_8 ==>
            linked t ==>
            sconst t_1 ==>
            sncmp_is_uint8 i_2 ==>
            sncmp_is_uint8 i_3 ==>
            sncmp_is_sint32 i ==>
            sncmp_is_uint64 i_1 ==>
            addr_le a_1 a ==>
            addr_le a_3 a_2 ==>
            sncmp_p_valid_strn t t_1 a_1 i_1 ==>
            sncmp_p_valid_strn t t_1 a_3 i_1 ==>
            sncmp_is_uint64 x_4 ==>
            addr_le a (sncmp_shift a_1 x_5) ==>
            addr_le a_2 (sncmp_shift a_3 x_7) ==>
            sncmp_p_valid_strn t t_1 a x_4 ==>
            sncmp_p_valid_strn t t_1 a_2 x_4 ==>
            (if x_8 = x_2 then
               i = 0
             else
               to_uint8 (t_1 a) = i_2 /\
               to_uint8 (t_1 a_2) = i_3 /\
               (if i_3 = i_2 then
                  i = 0 /\ i_3 = 0
                else if i_3 < i_2 then
                  i = -1
                else
                  i = 1) /\
               (i_2 = 0 ==>
                x_5 = l_strlen t_1 a_1 /\
                x_6 = x_2 /\
                sncmp_p_valid_str t t_1 a_1) /\
               (i_3 = 0 ==>
                x_7 = l_strlen t_1 a_3 /\
                x + x_7 = x_2 /\
                sncmp_p_valid_str t t_1 a_3)) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 < x_7 ==>
              t_1 (sncmp_shift a_3 i_4) =
              t_1 (sncmp_shift a_1 i_4)) ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 + x < x_2 ==>
              t_1 (sncmp_shift a_3 i_4) =
              t_1 (sncmp_shift a_1 i_4)) ==>
            (!i_4 : int.
              let x_9 = t_1 (sncmp_shift a_3 i_4) in
              let x_10 = t_1 (sncmp_shift a_1 i_4) in
                0 <= i_4 ==>
                i_4 < x_7 ==>
                (to_uint8 x_9 = to_uint8 x_10 <=>
                 x_9 = x_10)) ==>
            i = 1``;
