(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_PolicyInformation_Why3_ide_VCparse_PolicyInformation_loop_inv_preserved_goal2:
  an X.509 PolicyInformation parser loop-invariant preservation condition
  asserting validity of the remaining input-memory read under the stated
  address, allocation, and unsigned-integer bounds. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let pi_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let pi_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let pi_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let pi_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 a : int # int.
      !i_4 i_5 i i_1 i_2 i_3 : int.
      !a_2 : int # int.
      !i_6 : int.
      !t : int -> int.
        let x = FST a_1 in
        let x_1 = FST a in
        let a_3 = pi_shift a_1 i_4 in
        let a_4 = pi_shift a_1 (i_4 + i_5 - i) in
        let x_3 = i_4 + i_5 in
        let x_4 = i_1 - i_2 in
          i <> 0 ==>
          i_1 <> 0 ==>
          i_3 <> 0 ==>
          i_5 <> 0 ==>
          (0, 0) <> a_1 ==>
          (0, 0) <> a_2 ==>
          x <> x_1 ==>
          a_3 <> (0, 0) ==>
          a_4 <> (0, 0) ==>
          0 <= i ==>
          i_6 <= i ==>
          0 <= i_1 ==>
          i_2 <= i_1 ==>
          0 <= i_3 ==>
          i_4 <= i_3 ==>
          i_5 <= i_3 ==>
          0 <= i_5 ==>
          0 <= i_6 ==>
          x_3 <= i_3 ==>
          0 <= x_3 ==>
          region x_1 <= 0 ==>
          region x <= 0 ==>
          (-2147483648) <= i ==>
          (-2147483648) <= i_6 ==>
          2 <= i_2 ==>
          2 <= i_4 ==>
          i <= 65535 ==>
          i_6 <= 65535 ==>
          i <= 2147483647 ==>
          i_6 <= 2147483647 ==>
          (-2147483648) <= x_3 ==>
          x_3 <= 65535 ==>
          x_3 <= 2147483647 ==>
          2 + i_6 <= i ==>
          i_1 <= 65535 + i_2 ==>
          i_1 <= 2147483647 + i_2 ==>
          i_2 <= 2147483648 + i_1 ==>
          3 + i <= i_5 ==>
          linked t ==>
          pi_is_uint16 i ==>
          pi_is_uint16 i_1 ==>
          pi_is_uint16 i_2 ==>
          pi_is_uint16 i_3 ==>
          pi_is_uint16 i_4 ==>
          pi_is_uint16 i_5 ==>
          pi_is_uint16 i_6 ==>
          pi_valid_rw t a 1 ==>
          pi_is_uint16 (i - i_6) ==>
          pi_is_uint16 x_4 ==>
          pi_is_uint16 (i_5 - i) ==>
          pi_valid_rd t (pi_shift a_2 0) i_1 ==>
          (0 < i_3 ==> pi_valid_rd t (pi_shift a_1 0) i_3) ==>
          (0 < i_5 ==> pi_valid_rd t a_3 i_5) ==>
          (0 < i ==> pi_valid_rd t a_4 i) ==>
          pi_valid_rd t (pi_shift a_2 i_2) x_4``;
