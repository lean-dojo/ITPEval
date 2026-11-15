(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncat_Why3_ide_VCstrncat_loop_inv_2_preserved_goal4:
  a strncat loop-invariant preservation verification condition concluding
  that the address after the current non-null byte remains a valid C string,
  under the stated bounded-length, memory, address-order, byte-range, and
  no-earlier-null-byte assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
  ``let snc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let snc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let snc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let snc_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let snc_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (snc_shift s n) = 0 /\
          snc_is_uint64 n /\
          snc_valid_rw malloc (snc_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            snc_is_sint8 (mchar (snc_shift s j)))
    in
    let snc_p_valid_strn =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \cnt : int.
        snc_valid_rw malloc (snc_shift s 0) (1 + cnt) \/
        ((?n : int.
            mchar (snc_shift s n) = 0 /\
            n < cnt /\
            snc_is_uint64 n /\
            snc_valid_rw malloc (snc_shift s 0) (1 + n)) /\
         (!j : int.
           j <= cnt ==>
           snc_is_sint8 (mchar (snc_shift s j))))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
      !l_strnlen :
        ((int # int) -> int) -> (int # int) -> int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          snc_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          snc_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (snc_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (snc_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          snc_is_uint64 (l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          (if cnt = 0 \/ mchar (snc_shift s 0) = 0 then
             l_strnlen mchar s cnt = 0
           else
             to_uint64
               (1 +
                l_strnlen mchar (snc_shift s 1)
                  (to_uint64 (cnt - 1))) =
             l_strnlen mchar s cnt)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
         !cnt : int.
          snc_is_uint64 (l_strnlen mchar s cnt)) ==>
        !t_1 : (int # int) -> int.
        !a_2 a a_1 : int # int.
        !i : int.
        !t : int -> int.
          let x = t_1 a_2 in
          let x_1 = l_strlen t_1 a in
          let a_3 = snc_shift a x_1 in
          let x_2 = l_strnlen t_1 a_1 i in
          let x_3 = t_1 (snc_shift a_1 x_2) in
            i <> 0 ==>
            x <> 0 ==>
            t_1 a_3 = 0 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            i + x_1 <= 18446744073709551615 ==>
            linked t ==>
            sconst t_1 ==>
            snc_is_uint64 i ==>
            addr_le a a_2 ==>
            snc_is_sint8 x ==>
            snc_p_valid_str t t_1 a ==>
            snc_p_valid_str t t_1 a_2 ==>
            snc_is_uint64 x_1 ==>
            snc_p_valid_strn t t_1 a_1 i ==>
            snc_is_uint64 x_2 ==>
            addr_le a_2 a_3 ==>
            snc_is_sint8 x_3 ==>
            snc_valid_rw t (snc_shift a 0) (1 + i + x_1) ==>
            ((!i_1 : int.
                0 <= i_1 ==>
                i_1 <= i ==>
                t_1 (snc_shift a_1 i_1) <> 0) ==>
             x_2 = i) ==>
            ((?i_1 : int.
                t_1 (snc_shift a_1 i_1) = 0 /\
                0 <= i_1 /\
                i_1 <= i) ==>
             x_3 = 0) ==>
            ((?i_1 : int.
                t_1 (snc_shift a_1 i_1) = 0 /\
                0 <= i_1 /\
                i_1 <= i) ==>
             (!i_1 : int.
               0 <= i_1 ==>
               i_1 < x_2 ==>
               t_1 (snc_shift a_1 i_1) <> 0)) ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 < x_1 ==>
              t_1 (snc_shift a i_1) <> 0) ==>
            snc_p_valid_str t t_1 (snc_shift a_2 1)``;
