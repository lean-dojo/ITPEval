(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5:
  an X.509 arc parser verification condition asserting validity of a
  one-byte memory read after bounded traversal of a valid address range.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory int_bitwiseTheory;

val goal5 =
  ``let pa_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let pa_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let pa_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let pa_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
    let pa_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let pa_to_uint32 =
      \z : int. z % 4294967296
    in
    let pa_lsl =
      \z : int. \n : int. int_shift_left (Num n) z
    in
    let pa_bit_test =
      \z : int. \n : int. int_bit (Num n) z
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 a a_2 : int # int.
      !i_1 i i_2 : int.
      !t : int -> int.
      !t_1 : (int # int) -> int.
        let x = FST a_1 in
        let x_1 = FST a in
        let x_2 = FST a_2 in
          i_1 <> 0 ==>
          a_2 <> a ==>
          (0, 0) <> a_1 ==>
          x <> x_1 ==>
          x_2 <> x ==>
          0 <= i ==>
          0 <= i_1 ==>
          region x_1 <= 0 ==>
          region x <= 0 ==>
          region x_2 <= 0 ==>
          i_2 < pa_lsl 1 (pa_to_uint32 (7 * i)) ==>
          i <= 3 ==>
          i <= 4 ==>
          5 <= i_1 ==>
          pa_lsl i_2 7 <= 4294967295 ==>
          linked t ==>
          pa_is_uint16 i ==>
          pa_is_uint16 i_1 ==>
          pa_is_uint32 i_2 ==>
          pa_valid_rw t a 1 ==>
          pa_valid_rw t a_2 1 ==>
          (0 < i_1 ==> pa_valid_rd t (pa_shift a_1 0) i_1) ==>
          (!i_3 : int.
            0 <= i_3 ==>
            i_3 < i ==>
            pa_bit_test (t_1 (pa_shift a_1 i_3)) 7) ==>
          pa_valid_rd t (pa_shift a_1 i) 1``;
