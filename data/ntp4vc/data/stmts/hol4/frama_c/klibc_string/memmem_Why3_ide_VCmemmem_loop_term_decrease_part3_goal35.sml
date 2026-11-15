(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35:
  a memmem loop-termination decrease condition asserting growth of the
  incremented unsigned index, under integer-range, byte-memory, writable-region,
  separation, linking, region, and prior-loop assumptions. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal35 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mc_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. mc_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          mc_is_uint32 z ==>
          to_uint32 z = z) ==>
        !a_8 a_9 : int # int.
        !t_1 : (int # int) -> int.
        !a_1 a : int # int.
        !i_2 : int.
        !a_6 : int # int.
        !i_1 : int.
        !a_7 : int # int.
        !i : int.
        !t : int -> int.
        !a_5 a_4 a_3 a_2 : int # int.
          let x = FST a_8 in
          let x_1 = FST a_9 in
          let x_2 = t_1 (mc_shift a_1 0) in
          let x_3 = t_1 (mc_shift a i_2) in
          let x_4 = t_1 (mc_shift a_1 1) in
          let x_5 = to_uint32 (1 + i_2) in
          let x_6 = t_1 (mc_shift a x_5) in
          let a_10 = mc_shift a_8 0 in
          let a_11 = mc_shift a_9 0 in
          let a_12 = mc_shift a_6 0 in
          let x_7 = to_uint32 (i_1 - 2) in
          let a_13 = mc_shift a_7 0 in
            i <> 0 ==>
            i_1 <> 0 ==>
            i_1 <> 1 ==>
            x = FST a_1 ==>
            x_1 = FST a ==>
            x_2 <> x_3 ==>
            x_4 = x_2 ==>
            x_6 = x_4 ==>
            0 <= i ==>
            i_1 <= i ==>
            0 <= i_1 ==>
            0 <= i_2 ==>
            region x <= 0 ==>
            region x_1 <= 0 ==>
            i_2 <= to_uint32 (i - i_1) ==>
            i_1 + i_2 <= 2 + i ==>
            linked t ==>
            mc_is_uint32 i ==>
            mc_is_uint32 i_1 ==>
            mc_is_uint32 i_2 ==>
            mc_is_uint8 x_3 ==>
            mc_is_uint8 x_2 ==>
            mc_is_uint8 x_4 ==>
            mc_valid_rw t a_10 i_1 ==>
            mc_valid_rw t a_11 i ==>
            mc_separated a_11 i a_10 i_1 ==>
            mc_valid_rw t a_12 x_7 ==>
            mc_valid_rw t a_13 x_7 ==>
            mc_separated a_13 x_7 a_12 x_7 ==>
            mc_is_uint8 x_6 ==>
            (0 < x_7 ==>
             ~(?i_3 : int.
                t_1 (mc_shift a_5 i_3) <>
                  t_1 (mc_shift a_4 i_3) /\
                0 <= i_3 /\
                i_3 < x_7)) ==>
            (!i_3 : int.
              0 <= i_3 ==>
              i_3 < i_2 ==>
              (?i_4 : int.
                0 <= i_4 ==>
                3 + i_4 <= i_1 ==>
                t_1 (mc_shift a_3 (2 + i_4 + i_3)) <>
                  t_1 (mc_shift a_2 (2 + i_4)))) ==>
            i_2 < x_5``;
