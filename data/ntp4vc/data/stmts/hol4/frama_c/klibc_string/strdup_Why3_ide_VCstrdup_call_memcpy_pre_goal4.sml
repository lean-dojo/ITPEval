(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4:
  a strdup call-to-memcpy precondition verification condition concluding
  separation of source and destination string-sized memory regions from
  string-length, integer-range, writable-memory, linking, constancy, and
  non-null destination assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
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
    let mc_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mc_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !sconst : ((int # int) -> int) -> bool.
      !l_length : ((int # int) -> int) -> (int # int) -> int.
      !to_uint32 : int -> int.
        (!malloc : int -> int.
         !mchar : (int # int) -> int.
         !s : int # int.
         !n : int.
          mc_length_of_str_is malloc mchar s n ==>
          l_length mchar s = n) ==>
        (!z : int. mc_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          mc_is_uint32 z ==>
          to_uint32 z = z) ==>
        !t_1 : (int # int) -> int.
        !a a_1 : int # int.
        !t : int -> int.
        !i i_1 i_2 : int.
          let x = l_length t_1 a in
          let x_1 = 1 + x in
          let x_2 = to_uint32 x_1 in
          let a_2 = mc_shift a_1 0 in
            ((0 : int), (0 : int)) <> a_1 ==>
            x_2 <> 0 ==>
            region (FST a) <= 0 ==>
            linked t ==>
            sconst t_1 ==>
            mc_is_sint32 x ==>
            mc_length_of_str_is t t_1 a i ==>
            mc_length_of_str_is t t_1 a i_1 ==>
            mc_length_of_str_is t t_1 a i_2 ==>
            mc_is_sint32 x_1 ==>
            (0 < x_2 ==> mc_valid_rw t a_2 x_2) ==>
            mc_separated (mc_shift a 0) x_2 a_2 x_2``;
