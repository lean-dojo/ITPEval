(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14:
  an X.509 length parser verification condition asserting validity of a
  one-byte memory read two bytes after the input address under the stated
  allocation, integer-range, and bit conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory int_bitwiseTheory;

val goal14 =
  ``let gl_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let gl_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let gl_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let gl_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
    let gl_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 a a_2 : int # int.
      !t_1 : (int # int) -> int.
      !i : int.
      !t : int -> int.
        let x = FST a_1 in
        let x_1 = FST a in
        let x_2 = FST a_2 in
        let a_3 = gl_shift a_1 0 in
        let x_3 = t_1 a_3 in
          i <> 0 ==>
          a_2 <> a ==>
          (0, 0) <> a_1 ==>
          x <> x_1 ==>
          x_2 <> x ==>
          x_3 <> 128 ==>
          int_and 127 x_3 = 2 ==>
          0 <= i ==>
          region x_1 <= 0 ==>
          region x <= 0 ==>
          region x_2 <= 0 ==>
          3 <= i ==>
          linked t ==>
          gl_is_uint16 i ==>
          gl_valid_rw t a 1 ==>
          gl_valid_rw t a_2 1 ==>
          gl_is_uint8 x_3 ==>
          int_bit 7 x_3 ==>
          gl_valid_rd t a_3 1 ==>
          (0 < i ==> gl_valid_rd t a_3 i) ==>
          gl_valid_rd t (gl_shift a_1 2) 1``;
