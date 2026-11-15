(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_6_preserved_goal12:
  a strncmp sixth loop-invariant preservation verification condition
  concluding the updated bounded-string length equation after advancing the
  third address by one byte and decrementing the comparison count, under the
  stated memory, length, byte-range, address-order, and prefix-equality
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal12 =
  ``let strncmp_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strncmp_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strncmp_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let strncmp_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strncmp_is_sint64 =
      \z : int. -9223372036854775808 <= z /\
                z < 9223372036854775808
    in
    let strncmp_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strncmp_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        strncmp_valid_rw malloc (strncmp_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (strncmp_shift s n) = 0 /\
            n < cnt /\
            strncmp_is_uint64 n /\
            strncmp_valid_rw malloc (strncmp_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           strncmp_is_sint8 (mchar (strncmp_shift s j))))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint8 to_sint8 to_uint64 to_sint64 : int -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          strncmp_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          strncmp_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          strncmp_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          strncmp_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          strncmp_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strncmp_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          strncmp_is_sint64 (to_sint64 z)) ==>
        (!z : int.
          strncmp_is_sint64 z ==>
          to_sint64 z = z) ==>
        (!z : int.
          to_sint8 (to_uint8 z) = to_sint8 z) ==>
        (!z : int.
          to_sint64 (to_uint64 z) = to_sint64 z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (strncmp_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (strncmp_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          strncmp_is_uint64 (l_strnlen mchar s cnt)) ==>
        !t_1 : (int # int) -> int.
        !a_2 a_3 a_1 a : int # int.
        !i : int.
        !t : int -> int.
          let x = t_1 a_2 in
          let x_1 = to_uint8 x in
          let x_2 = t_1 a_3 in
          let x_3 = SND a_1 in
          let x_4 = SND a_3 in
          let x_5 = SND a in
          let x_6 = SND a_2 in
          let x_7 = x_4 - x_5 in
          let x_8 = t_1 (strncmp_shift a_1 x_7) in
          let x_9 = t_1 (strncmp_shift a x_7) in
          let x_10 = i + x_6 - x_3 in
          let x_11 = l_strnlen t_1 a x_10 in
          let x_12 = x_5 + x_11 in
          let x_13 = l_strnlen t_1 a_1 x_10 in
            ~(i = 0) ==>
            ~(x_1 = 0) ==>
            to_uint8 x_2 = x_1 ==>
            x_3 + x_4 = x_5 + x_6 ==>
            x_8 = x_9 ==>
            x_12 = x_4 + l_strnlen t_1 a_3 i ==>
            x_3 + x_13 = x_6 + l_strnlen t_1 a_2 i ==>
            0 <= i ==>
            x_3 <= x_6 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            strncmp_is_uint64 i ==>
            addr_le a a_3 ==>
            addr_le a_1 a_2 ==>
            strncmp_is_sint8 x ==>
            strncmp_is_sint8 x_2 ==>
            strncmp_p_valid_strn t t_1 a_2 i ==>
            strncmp_p_valid_strn t t_1 a_3 i ==>
            strncmp_is_uint64 x_10 ==>
            strncmp_is_sint8 x_9 ==>
            strncmp_is_sint8 x_8 ==>
            strncmp_p_valid_strn t t_1 a x_10 ==>
            strncmp_p_valid_strn t t_1 a_1 x_10 ==>
            addr_le a_2 (strncmp_shift a_1 x_13) ==>
            addr_le a_3 (strncmp_shift a x_11) ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 + x_3 < x_6 ==>
              t_1 (strncmp_shift a_1 i_1) =
              t_1 (strncmp_shift a i_1)) ==>
            (!i_1 : int.
              let x_14 = t_1 (strncmp_shift a_1 i_1) in
              let x_15 = t_1 (strncmp_shift a i_1) in
                0 <= i_1 ==>
                i_1 < x_11 ==>
                (to_uint8 x_14 = to_uint8 x_15 <=>
                 x_14 = x_15)) ==>
            x_12 =
              1 + x_4 +
              l_strnlen t_1 (strncmp_shift a_3 1)
                (to_uint64 (i - 1))``;
