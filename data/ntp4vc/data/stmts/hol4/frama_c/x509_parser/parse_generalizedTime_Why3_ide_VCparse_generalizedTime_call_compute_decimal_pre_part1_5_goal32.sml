(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_decimal_pre_part1_5_goal32:
  an X.509 generalized-time parser verification condition concluding that the
  byte at offset fourteen is at least the ASCII digit lower bound, under the
  stated address, memory-validity, separation, integer-range, and
  preceding-digit assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal32 =
  ``let gen_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let gen_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let gen_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let gen_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        ~(FST p = FST q) \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let gen_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let gen_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_7 : int # int.
      !t_1 : (int # int) -> int.
      !a_1 a a_2 a_3 a_4 a_5 a_6 : int # int.
      !i i_2 i_3 i_4 i_5 i_6 i_1 : int.
      !t : int -> int.
        let a_8 = gen_shift a_7 0 in
        let a_9 = gen_shift a_7 1 in
        let a_10 = gen_shift a_7 16 in
        let a_11 = gen_shift a_7 2 in
        let x = t_1 a_11 in
        let a_12 = gen_shift a_7 3 in
        let x_1 = t_1 a_12 in
        let a_13 = gen_shift a_7 4 in
        let x_2 = t_1 a_13 in
        let a_14 = gen_shift a_7 5 in
        let x_3 = t_1 a_14 in
        let a_15 = gen_shift a_7 6 in
        let x_4 = t_1 a_15 in
        let a_16 = gen_shift a_7 7 in
        let x_5 = t_1 a_16 in
        let a_17 = gen_shift a_7 8 in
        let x_6 = t_1 a_17 in
        let a_18 = gen_shift a_7 9 in
        let x_7 = t_1 a_18 in
        let a_19 = gen_shift a_7 10 in
        let x_8 = t_1 a_19 in
        let a_20 = gen_shift a_7 11 in
        let x_9 = t_1 a_20 in
        let a_21 = gen_shift a_7 12 in
        let x_10 = t_1 a_21 in
        let a_22 = gen_shift a_7 13 in
        let x_11 = t_1 a_22 in
        let a_23 = gen_shift a_7 14 in
        let x_12 = t_1 a_23 in
        let a_24 = gen_shift a_7 15 in
          a_1 <> a ==>
          a_2 <> a ==>
          a_2 <> a_1 ==>
          a_3 <> a ==>
          a_3 <> a_1 ==>
          a_3 <> a_2 ==>
          a_4 <> a ==>
          a_4 <> a_1 ==>
          a_4 <> a_2 ==>
          a_4 <> a_3 ==>
          a_5 <> a ==>
          a_5 <> a_1 ==>
          a_5 <> a_2 ==>
          a_5 <> a_3 ==>
          a_5 <> a_4 ==>
          a_6 <> a ==>
          a_6 <> a_1 ==>
          a_6 <> a_2 ==>
          a_6 <> a_3 ==>
          a_6 <> a_4 ==>
          a_6 <> a_5 ==>
          (0, 0) <> a_7 ==>
          t_1 a_8 = 24 ==>
          t_1 a_9 = 15 ==>
          t_1 a_10 = 90 ==>
          0 <= i ==>
          0 <= i_2 ==>
          0 <= i_3 ==>
          0 <= i_4 ==>
          0 <= i_5 ==>
          0 <= i_6 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          region (FST a_5) <= 0 ==>
          region (FST a_6) <= 0 ==>
          region (FST a_7) <= 0 ==>
          14 <= i_1 ==>
          17 <= i ==>
          i_3 <= 99 ==>
          i_4 <= 99 ==>
          i_5 <= 99 ==>
          i_6 <= 99 ==>
          i_2 <= 9999 ==>
          48 <= x ==>
          48 <= x_1 ==>
          48 <= x_2 ==>
          48 <= x_3 ==>
          48 <= x_4 ==>
          48 <= x_5 ==>
          48 <= x_6 ==>
          48 <= x_7 ==>
          48 <= x_8 ==>
          48 <= x_9 ==>
          48 <= x_10 ==>
          48 <= x_11 ==>
          x <= 57 ==>
          x_1 <= 57 ==>
          x_2 <= 57 ==>
          x_3 <= 57 ==>
          x_4 <= 57 ==>
          x_5 <= 57 ==>
          x_6 <= 57 ==>
          x_7 <= 57 ==>
          x_8 <= 57 ==>
          x_9 <= 57 ==>
          x_10 <= 57 ==>
          x_11 <= 57 ==>
          linked t ==>
          gen_is_uint8 i_1 ==>
          gen_is_uint8 i_3 ==>
          gen_is_uint8 i_4 ==>
          gen_is_uint8 i_5 ==>
          gen_is_uint8 i_6 ==>
          gen_is_uint16 i ==>
          gen_is_uint16 i_2 ==>
          gen_valid_rw t a 1 ==>
          gen_valid_rw t a_1 1 ==>
          gen_valid_rw t a_2 1 ==>
          gen_valid_rw t a_3 1 ==>
          gen_valid_rw t a_4 1 ==>
          gen_valid_rw t a_5 1 ==>
          gen_valid_rw t a_6 1 ==>
          gen_is_uint8 x ==>
          gen_is_uint8 x_1 ==>
          gen_is_uint8 x_2 ==>
          gen_is_uint8 x_3 ==>
          gen_is_uint8 x_4 ==>
          gen_is_uint8 x_5 ==>
          gen_is_uint8 x_6 ==>
          gen_is_uint8 x_7 ==>
          gen_is_uint8 x_8 ==>
          gen_is_uint8 x_9 ==>
          gen_is_uint8 x_10 ==>
          gen_is_uint8 x_11 ==>
          gen_is_uint8 x_12 ==>
          gen_is_uint8 (t_1 a_24) ==>
          gen_valid_rd t a_8 1 ==>
          gen_valid_rd t a_9 1 ==>
          gen_valid_rd t a_11 1 ==>
          gen_valid_rd t a_12 1 ==>
          gen_valid_rd t a_13 1 ==>
          gen_valid_rd t a_14 1 ==>
          gen_valid_rd t a_15 1 ==>
          gen_valid_rd t a_16 1 ==>
          gen_valid_rd t a_17 1 ==>
          gen_valid_rd t a_18 1 ==>
          gen_valid_rd t a_19 1 ==>
          gen_valid_rd t a_20 1 ==>
          gen_valid_rd t a_21 1 ==>
          gen_valid_rd t a_22 1 ==>
          gen_valid_rd t a_23 1 ==>
          gen_valid_rd t a_24 1 ==>
          gen_valid_rd t a_10 1 ==>
          gen_separated a 1 a_8 i ==>
          gen_separated a_1 1 a_8 i ==>
          gen_separated a_2 1 a_8 i ==>
          gen_separated a_3 1 a_8 i ==>
          gen_separated a_4 1 a_8 i ==>
          gen_separated a_5 1 a_8 i ==>
          gen_separated a_6 1 a_8 i ==>
          gen_valid_rd t (gen_shift a_7 (2 + i_1)) 1 ==>
          (0 < i ==> gen_valid_rd t a_8 i) ==>
          (!i_7 : int.
            let x_13 = t_1 (gen_shift a_7 (2 + i_7)) in
              0 <= i_7 ==>
              i_7 < i_1 ==>
              48 <= x_13 /\ x_13 <= 57) ==>
          48 <= x_12``;
