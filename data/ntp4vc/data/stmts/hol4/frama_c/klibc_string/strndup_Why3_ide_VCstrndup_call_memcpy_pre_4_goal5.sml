(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5:
  a strndup call-to-memcpy precondition verification condition concluding
  writability of the source region for the selected length, under unsigned
  integer-range, memory-validity, linking, constancy, and first-null-position
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal5 =
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
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. mc_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          mc_is_uint32 z ==>
          to_uint32 z = z) ==>
        !i_1 : int.
        !a a_1 : int # int.
        !i : int.
        !t : int -> int.
        !t_1 : (int # int) -> int.
          let x = to_uint32 (1 + i_1) in
          let a_2 = mc_shift a 0 in
            ((0 : int), (0 : int)) <> a_1 ==>
            x <> 0 ==>
            0 <= i ==>
            region (FST a) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_uint32 i ==>
            mc_is_uint32 i_1 ==>
            mc_valid_rw t a_2 i ==>
            (0 < x ==>
              mc_valid_rw t (mc_shift a_1 0) x) ==>
            ((!i_2 : int.
              0 <= i_2 ==>
              i_2 < i ==>
              t_1 (mc_shift a i_2) <> 0) ==>
              i_1 = i) ==>
            ((?i_2 : int.
              t_1 (mc_shift a i_2) = 0 /\
              0 <= i_2 /\
              i_2 < i) ==>
              i_1 <= i) ==>
            mc_valid_rw t a_2 i_1``;
