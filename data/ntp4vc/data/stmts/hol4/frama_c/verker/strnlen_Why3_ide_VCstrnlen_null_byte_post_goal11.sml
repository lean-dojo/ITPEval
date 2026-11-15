(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strnlen_Why3_ide_VCstrnlen_null_byte_post_goal11:
  a bounded-string-length null-byte postcondition verification condition
  concluding that the uint64-shifted byte is null, under the stated memory,
  address-order, byte-range, bounded-string-validity, length, and
  no-earlier-null-byte assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal11 =
  ``let strnlen_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strnlen_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strnlen_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strnlen_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strnlen_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        strnlen_valid_rw malloc (strnlen_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (strnlen_shift s n) = 0 /\
            n < cnt /\
            strnlen_is_uint64 n /\
            strnlen_valid_rw malloc (strnlen_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           strnlen_is_sint8 (mchar (strnlen_shift s j))))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          strnlen_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strnlen_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (strnlen_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (strnlen_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          strnlen_is_uint64 (l_strnlen mchar s cnt)) ==>
        !a a_1 : int # int.
        !i_1 : int.
        !t_1 : (int # int) -> int.
        !i : int.
        !t : int -> int.
          let x = SND a in
          let x_1 = SND a_1 in
          let x_2 = i_1 + x_1 - x in
          let x_3 = l_strnlen t_1 a_1 i_1 in
          let x_4 = i_1 + x_1 in
          let x_5 =
            t_1 (strnlen_shift a_1 (to_uint64 (x - x_1)))
          in
            t_1 (strnlen_shift a_1 i) = 0 ==>
            x + l_strnlen t_1 a x_2 = x_1 + x_3 ==>
            0 <= i ==>
            i <= i_1 ==>
            x_1 <= x ==>
            region (FST a_1) <= 0 ==>
            x <= x_4 ==>
            linked t ==>
            sconst t_1 ==>
            strnlen_is_uint64 i_1 ==>
            addr_le a_1 a ==>
            strnlen_p_valid_strn t t_1 a_1 i_1 ==>
            strnlen_is_uint64 x_2 ==>
            addr_le a (strnlen_shift a_1 x_3) ==>
            strnlen_p_valid_strn t t_1 a x_2 ==>
            strnlen_is_sint8 x_5 ==>
            (t_1 a = 0 \/ x_4 = x) ==>
            (!i_2 : int.
              0 <= i_2 ==>
              i_2 + x_1 < x ==>
              ~(t_1 (strnlen_shift a_1 i_2) = 0)) ==>
            x_5 = 0``;
