(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strcat_Why3_ide_VCstrcat_loop_inv_2_preserved_goal3:
  a strcat loop-invariant preservation verification condition concluding
  validity of the string after the current non-null byte, under address-order,
  length, writable-memory, and preceding-non-null-byte assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal3 =
  ``let sc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let sc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let sc_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let sc_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (sc_shift s n) = 0 /\
          sc_is_uint64 n /\
          sc_valid_rw malloc (sc_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            sc_is_sint8 (mchar (sc_shift s j)))
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int.
          sc_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          sc_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (sc_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (sc_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          sc_is_uint64 (l_strlen mchar s)) ==>
        !t_1 : (int # int) -> int.
        !a_2 a a_1 : int # int.
        !t : int -> int.
          let x = t_1 a_2 in
          let x_1 = l_strlen t_1 a in
          let a_3 = sc_shift a x_1 in
          let x_2 = l_strlen t_1 a_1 in
            x <> 0 ==>
            t_1 a_3 = 0 ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            x_1 + x_2 <= 18446744073709551615 ==>
            linked t ==>
            sconst t_1 ==>
            addr_le a a_2 ==>
            sc_is_sint8 x ==>
            sc_p_valid_str t t_1 a ==>
            sc_p_valid_str t t_1 a_1 ==>
            sc_p_valid_str t t_1 a_2 ==>
            sc_is_uint64 x_1 ==>
            addr_le a_2 a_3 ==>
            sc_valid_rw t (sc_shift a 0) (1 + x_1 + x_2) ==>
            (!i : int.
              0 <= i ==>
              i < x_1 ==>
              t_1 (sc_shift a i) <> 0) ==>
            (!i : int.
              0 <= i ==>
              i + SND a < SND a_2 ==>
              t_1 (sc_shift a i) <> 0) ==>
            sc_p_valid_str t t_1 (sc_shift a_2 1)``;
