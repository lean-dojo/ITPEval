(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_loop_inv_2_preserved_goal6:
  a string-trimming loop-invariant preservation verification condition
  concluding that the byte read from the source character memory at the
  second address is whitespace, under the stated memory, address-order,
  byte-range, valid-string, and intervening-whitespace assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal6 =
  ``let strim_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let strim_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let strim_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let strim_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let strim_is_uint64 =
      \z : int. 0 <= z /\ z < 18446744073709551616
    in
    let strim_p_isspace =
      \z : int.
        z = 9 \/ z = 10 \/ z = 12 \/ z = 13 \/ z = 32
    in
    let strim_p_valid_str =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
        ?n : int.
          mchar (strim_shift s n) = 0 /\
          strim_is_uint64 n /\
          strim_valid_rw malloc (strim_shift s 0) (1 + n) /\
          (!j : int.
            j <= n ==>
            strim_is_sint8 (mchar (strim_shift s j)))
    in
      !addr_le addr_lt : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint64 : int -> int.
      !l_strlen :
        ((int # int) -> int) -> (int # int) -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!p q : int # int.
          FST p = FST q ==>
          (addr_lt p q <=> SND p < SND q)) ==>
        (!z : int.
          strim_is_uint64 (to_uint64 z)) ==>
        (!z : int.
          strim_is_uint64 z ==>
          to_uint64 z = z) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          (if mchar (strim_shift s 0) = 0 then
             l_strlen mchar s = 0
           else
             to_uint64 (1 + l_strlen mchar (strim_shift s 1)) =
             l_strlen mchar s)) ==>
        (!mchar : (int # int) -> int.
         !s : int # int.
          strim_is_uint64 (l_strlen mchar s)) ==>
        !t_1 : (int # int) -> int.
        !a : int # int.
        !a_1 : int # int.
        !i : int.
        !t : int -> int.
        !a_2 : int # int.
          let x = l_strlen t_1 a in
          let a_3 = strim_shift a (x - 1) in
          let x_1 = t_1 a_3 in
          let x_2 = t_1 a_1 in
            ~(i = 0) ==>
            ~(x = 0) ==>
            t_1 (strim_shift a x) = 0 ==>
            ~(x_1 = 0) ==>
            0 < x ==>
            region (FST a) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            strim_is_uint8 i ==>
            addr_le a a_1 ==>
            strim_is_sint8 x_2 ==>
            strim_p_isspace x_2 ==>
            strim_p_valid_str t t_1 a ==>
            strim_is_uint64 x ==>
            addr_lt (strim_shift a_1 (-1)) a_2 ==>
            addr_le (strim_shift a (-1)) a_1 ==>
            addr_le a_1 a_3 ==>
            addr_le a_2 a_3 ==>
            strim_is_sint8 x_1 ==>
            (!i_1 : int.
              0 <= i_1 ==>
              i_1 < x ==>
              ~(t_1 (strim_shift a i_1) = 0)) ==>
            (!a_4 : int # int.
              addr_lt a_1 a_4 ==>
              addr_le a_4 a_3 ==>
              strim_p_isspace (t_1 a_4)) ==>
            strim_p_isspace (t_1 a_2)``;
