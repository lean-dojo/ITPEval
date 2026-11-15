(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9:
  a strcat call-to-strcpy precondition verification condition concluding
  separation of two string-sized memory regions from string-length,
  writable-memory, address-order, linking, constancy, and first-null-byte
  assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal9 =
  ``let mc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let mc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let mc_length_of_str_is =
      \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \n : int.
        mchar (mc_shift s n) = 0 /\
        0 <= n /\
        mc_valid_rw malloc (mc_shift s 0) (1 + n) /\
        (!j : int.
          0 <= j ==>
          j < n ==>
          mchar (mc_shift s j) <> 0)
    in
    let mc_is_sint8 =
      \z : int. -128 <= z /\ z < 128
    in
    let mc_exists_first_occurrence =
      \to_sint8 : int -> int.
       \l_length : ((int # int) -> int) -> (int # int) -> int.
       \malloc : int -> int.
       \mchar : (int # int) -> int.
       \s : int # int.
       \c : int.
       \pos : int.
        let byte = to_sint8 c in
        let len = l_length mchar s in
          mchar (mc_shift s pos) = byte /\
          0 <= pos /\
          pos <= len /\
          -128 <= c /\
          c <= 127 /\
          mc_valid_rw malloc (mc_shift s 0) (1 + len) /\
          (!j : int.
            0 <= j ==>
            j < pos ==>
            mchar (mc_shift s j) <> byte)
    in
      !addr_le : (int # int) -> (int # int) -> bool.
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !l_length : ((int # int) -> int) -> (int # int) -> int.
      !to_sint8 : int -> int.
        (!p q : int # int.
          FST p = FST q ==>
          (addr_le p q <=> SND p <= SND q)) ==>
        (!malloc : int -> int.
         !mchar : (int # int) -> int.
         !s : int # int.
         !n : int.
          mc_length_of_str_is malloc mchar s n ==>
          l_length mchar s = n) ==>
        (!z : int. mc_is_sint8 (to_sint8 z)) ==>
        (!z : int.
          mc_is_sint8 z ==>
          to_sint8 z = z) ==>
        !a_2 : int # int.
        !t_1 : (int # int) -> int.
        !a : int # int.
        !a_1 : int # int.
        !t : int -> int.
        !i i_3 i_1 i_2 i_4 : int.
          let x = FST a_2 in
          let x_1 = t_1 a in
          let a_3 = mc_shift a_2 0 in
          let x_2 = l_length t_1 a_1 in
          let x_3 = l_length t_1 a_2 in
          let a_4 = mc_shift a_1 0 in
          let x_4 = 1 + x_2 in
            region (FST a_1) <= 0 ==>
            region x <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_sint8 x_1 ==>
            mc_length_of_str_is t t_1 a_1 i ==>
            mc_length_of_str_is t t_1 a_1 i_3 ==>
            mc_length_of_str_is t t_1 a_2 i_1 ==>
            mc_length_of_str_is t t_1 a_2 i_2 ==>
            mc_length_of_str_is t t_1 a_2 i_4 ==>
            mc_valid_rw t a_3 (x_2 + x_3) ==>
            mc_separated a_3 (1 + x_3) a_4 x_4 ==>
            ((!i_5 : int.
              0 <= i_5 ==>
              i_5 < x_3 ==>
              t_1 (mc_shift a_2 i_5) <> 0) ==>
              ((0 : int), (0 : int)) = a) ==>
            ((?i_5 : int.
              t_1 (mc_shift a_2 i_5) = 0 /\
              0 <= i_5 /\
              i_5 < x_3) ==>
              x_1 = 0) ==>
            ((?i_5 : int.
              t_1 (mc_shift a_2 i_5) = 0 /\
              0 <= i_5 /\
              i_5 < x_3) ==>
              x = FST a) ==>
            ((?i_5 : int.
              t_1 (mc_shift a_2 i_5) = 0 /\
              0 <= i_5 /\
              i_5 < x_3) ==>
              mc_exists_first_occurrence
                to_sint8 l_length t t_1 a_2 0
                (SND a - SND a_2)) ==>
            ((?i_5 : int.
              t_1 (mc_shift a_2 i_5) = 0 /\
              0 <= i_5 /\
              i_5 < x_3) ==>
              addr_le a_2 a /\
              addr_le a (mc_shift a_2 x_3)) ==>
            mc_separated a_4 x_4 (mc_shift a 0) x_4``;
