(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29:
  an X.509 UTF-8 parser verification condition asserting validity of a
  one-byte read at the fourth byte under the stated byte-range, bit-mask,
  allocation, and prior memory-read assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory int_bitwiseTheory;

val goal29 =
  ``let utf8_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let utf8_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let utf8_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
    let utf8_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 : int # int.
      !t_1 : (int # int) -> int.
      !i i_1 : int.
      !a : int # int.
      !t : int -> int.
        let a_2 = utf8_shift a_1 0 in
        let a_3 = utf8_shift a_1 1 in
        let x = t_1 a_3 in
        let a_4 = utf8_shift a_1 2 in
        let x_1 = t_1 a_4 in
        let a_5 = utf8_shift a_1 3 in
          i <> 0 ==>
          i_1 <> 0 ==>
          (0, 0) <> a ==>
          t_1 a_2 = 244 ==>
          int_and 192 x = 128 ==>
          int_and 192 x_1 = 128 ==>
          0 <= i_1 ==>
          region (FST a) <= 0 ==>
          4 <= i ==>
          128 <= x ==>
          x <= 143 ==>
          linked t ==>
          utf8_is_uint16 i ==>
          utf8_is_uint16 i_1 ==>
          utf8_is_uint8 x ==>
          utf8_is_uint8 x_1 ==>
          utf8_is_uint8 (t_1 a_5) ==>
          utf8_valid_rd t a_2 1 ==>
          utf8_valid_rd t a_2 i ==>
          utf8_valid_rd t a_3 1 ==>
          utf8_valid_rd t a_4 1 ==>
          (0 < i_1 ==> utf8_valid_rd t (utf8_shift a 0) i_1) ==>
          utf8_valid_rd t a_5 1``;
