(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strnlen_Why3_ide_VCstrnlen_loop_inv_4_preserved_goal6:
  a bounded-string-length loop-invariant preservation verification condition
  concluding that advancing the current address by one preserves bounded
  string validity for the decremented uint64 count, under the stated memory,
  address-order, byte-range, length, and non-null-prefix assumptions. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal6 =
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
        !t_1 : (int # int) -> int.
        !a a_1 : int # int.
        !i : int.
        !t : int -> int.
          let x = t_1 a in
          let x_1 = SND a_1 in
          let x_2 = SND a in
          let x_3 = i + x_2 - x_1 in
          let x_4 = l_strnlen t_1 a_1 x_3 in
            ~(i = 0) ==>
            ~(x = 0) ==>
            x_1 + x_4 = x_2 + l_strnlen t_1 a i ==>
            0 <= i ==>
            x_1 <= x_2 ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            strnlen_is_uint64 i ==>
            addr_le a_1 a ==>
            strnlen_is_sint8 x ==>
            strnlen_p_valid_strn t t_1 a i ==>
            strnlen_is_uint64 x_3 ==>
            strnlen_p_valid_strn t t_1 a_1 x_3 ==>
            addr_le a (strnlen_shift a_1 x_4) ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 + x_1 < x_2 ==>
              ~(t_1 (strnlen_shift a_1 i_1) = 0)) ==>
            strnlen_p_valid_strn
              t t_1 (strnlen_shift a 1) (to_uint64 (i - 1))``;
