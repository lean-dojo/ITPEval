(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_7_part04_goal20:
  an X.509 UTF-8 parser verification condition asserting validity of a
  one-byte memory read after the current input address.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal20 =
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
        let x = t_1 a_2 in
          i <> 0 ==>
          i_1 <> 0 ==>
          (0, 0) <> a ==>
          x <> 240 ==>
          x <> 244 ==>
          0 <= i_1 ==>
          region (FST a) <= 0 ==>
          4 <= i ==>
          128 <= x ==>
          194 <= x ==>
          224 <= x ==>
          240 <= x ==>
          x <= 244 ==>
          linked t ==>
          utf8_is_uint16 i ==>
          utf8_is_uint16 i_1 ==>
          utf8_is_uint8 x ==>
          utf8_valid_rd t a_2 1 ==>
          utf8_valid_rd t a_2 i ==>
          (0 < i_1 ==> utf8_valid_rd t (utf8_shift a 0) i_1) ==>
          utf8_valid_rd t (utf8_shift a_1 1) 1``;
