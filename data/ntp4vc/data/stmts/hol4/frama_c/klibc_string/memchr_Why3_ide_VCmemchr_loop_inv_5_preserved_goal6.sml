(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6:
  a memchr loop-invariant preservation condition asserting that a selected
  byte differs from the searched byte, under integer-range, writable-memory,
  address-order, linking, constancy, and prior-byte assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal6 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let mc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_sint8 : int -> int.
      !to_uint32 : int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!z : int. mc_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          mc_is_sint8 z ==>
          to_sint8 z = z) ==>
        (!z : int. mc_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          mc_is_uint32 z ==>
          to_uint32 z = z) ==>
        !a : int # int.
        !i_1 i : int.
        !t_1 : (int # int) -> int.
        !i_3 i_2 : int.
        !t : int -> int.
          let a_1 = mc_shift a (i_1 - i) in
          let x = t_1 a_1 in
          let x_1 = to_sint8 i_3 in
            i <> 0 ==>
            x <> x_1 ==>
            0 < i_1 ==>
            0 <= i ==>
            i <= i_1 ==>
            0 <= i_2 ==>
            region (FST a) <= 0 ==>
            i_2 + to_uint32 (i - 1) < i_1 ==>
            -128 <= i_3 ==>
            i_3 <= 127 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_uint32 i ==>
            mc_is_uint32 i_1 ==>
            mc_is_sint32 i_3 ==>
            mc_valid_rw t (mc_shift a 0) i_1 ==>
            addr_le a a_1 ==>
            addr_le a_1 (mc_shift a i_1) ==>
            mc_is_sint8 x ==>
            (!i_4 : int.
              0 <= i_4 ==>
              i_4 + i < i_1 ==>
              t_1 (mc_shift a i_4) <> x_1) ==>
            t_1 (mc_shift a i_2) <> x_1``;
