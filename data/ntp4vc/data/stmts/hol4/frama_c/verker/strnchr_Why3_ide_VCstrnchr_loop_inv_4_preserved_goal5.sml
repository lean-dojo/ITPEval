(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strnchr_Why3_ide_VCstrnchr_loop_inv_4_preserved_goal5:
  a bounded-character-search loop-invariant preservation verification
  condition concluding that the next address and remaining bound form a valid
  bounded string, under the stated byte, address-order, memory, length, range,
  and no-earlier-match assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal5 =
  ``let snchr_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let snchr_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let snchr_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let snchr_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let snchr_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let snchr_is_sint64 =
      \z : int. -9223372036854775808 <= z /\
                z < 9223372036854775808
    in
    let snchr_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let snchr_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        snchr_valid_rw malloc (snchr_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (snchr_shift s n) = 0 /\
            n < cnt /\
            snchr_is_uint64 n /\
            snchr_valid_rw malloc (snchr_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           snchr_is_sint8 (mchar (snchr_shift s j))))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint8 to_sint8 to_uint64 to_sint64 : int -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          snchr_is_uint8 (to_uint8 z)) ==>
        (!z : int.
          snchr_is_uint8 z ==>
          to_uint8 z = z) ==>
        (!z : int.
          snchr_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          snchr_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int.
          snchr_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          snchr_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!z : int.
          snchr_is_sint64 (to_sint64 z)) ==>
        (!z : int.
          snchr_is_sint64 z ==>
          to_sint64 z = z) ==>
        (!z : int.
          to_sint8 (to_uint8 z) = to_sint8 z) ==>
        (!z : int.
          to_sint64 (to_uint64 z) = to_sint64 z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (snchr_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (snchr_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          snchr_is_uint64 (l_strnlen mchar s cnt)) ==>
        !t_1 : (int # int) -> int.
        !a : int # int.
        !i_1 : int.
        !a_1 : int # int.
        !i : int.
        !t : int -> int.
          let x = t_1 a in
          let x_1 = to_sint8 i_1 in
          let x_2 = SND a_1 in
          let x_3 = i + x_2 in
          let x_4 = SND a in
          let x_6 = i + x_2 - x_4 in
          let x_7 = l_strnlen t_1 a_1 i in
            ~(x = 0) ==>
            ~(x = x_1) ==>
            ~(x_3 = x_4) ==>
            x_4 + l_strnlen t_1 a x_6 = x_2 + x_7 ==>
            x_2 <= x_4 ==>
            region (FST a_1) <= 0 ==>
            x_4 <= x_3 ==>
            linked t ==>
            sconst t_1 ==>
            snchr_is_sint32 i_1 ==>
            snchr_is_uint64 i ==>
            addr_le a_1 a ==>
            snchr_is_sint8 x ==>
            snchr_p_valid_strn t t_1 a_1 i ==>
            snchr_is_uint64 x_6 ==>
            addr_le a (snchr_shift a_1 x_7) ==>
            snchr_p_valid_strn t t_1 a x_6 ==>
            (!a_2 : int # int.
              addr_lt a_2 a ==>
              addr_le a_1 a_2 ==>
              ~(t_1 a_2 = x_1)) ==>
            snchr_p_valid_strn t t_1 (snchr_shift a 1)
              (to_uint64 (i + x_2 - 1 - x_4))``;
