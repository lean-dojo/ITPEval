(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_UTCTime_Why3_ide_VCparse_UTCTime_call_compute_decimal_pre_part1_3_goal17:
  an X.509 UTC-time parser verification condition concluding that the byte at
  offset six is at least the ASCII digit lower bound, under the stated address,
  memory-validity, separation, integer-range, and preceding-digit assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal17 =
  ``let utc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let utc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let utc_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        ~(0 = FST p) /\
        0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let utc_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/
        m <= 0 \/
        ~(FST p = FST q) \/
        SND q + m <= SND p \/
        SND p + n <= SND q
    in
    let utc_is_uint8 =
      \z : int. 0 <= z /\ z < 256
    in
    let utc_is_uint16 =
      \z : int. 0 <= z /\ z < 65536
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_7 : int # int.
      !t_1 : (int # int) -> int.
      !a_1 a a_2 a_3 a_4 a_5 a_6 : int # int.
      !i i_1 i_3 i_2 : int.
      !t : int -> int.
        let a_8 = utc_shift a_7 0 in
        let a_9 = utc_shift a_7 1 in
        let a_10 = utc_shift a_7 14 in
        let a_11 = utc_shift a_7 2 in
        let x = t_1 a_11 in
        let a_12 = utc_shift a_7 3 in
        let x_1 = t_1 a_12 in
        let a_13 = utc_shift a_7 4 in
        let x_2 = t_1 a_13 in
        let a_14 = utc_shift a_7 5 in
        let x_3 = t_1 a_14 in
        let a_15 = utc_shift a_7 6 in
        let x_4 = t_1 a_15 in
        let a_16 = utc_shift a_7 7 in
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
          t_1 a_8 = 23 ==>
          t_1 a_9 = 13 ==>
          t_1 a_10 = 90 ==>
          0 <= i ==>
          0 <= i_1 ==>
          0 <= i_3 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          region (FST a_3) <= 0 ==>
          region (FST a_4) <= 0 ==>
          region (FST a_5) <= 0 ==>
          region (FST a_6) <= 0 ==>
          region (FST a_7) <= 0 ==>
          (-1900) <= i ==>
          12 <= i_2 ==>
          15 <= i_1 ==>
          50 <= i ==>
          i <= 99 ==>
          i_3 <= 99 ==>
          i <= 63635 ==>
          i <= 2147481747 ==>
          48 <= x ==>
          48 <= x_1 ==>
          48 <= x_2 ==>
          48 <= x_3 ==>
          x <= 57 ==>
          x_1 <= 57 ==>
          x_2 <= 57 ==>
          x_3 <= 57 ==>
          linked t ==>
          utc_is_uint8 i ==>
          utc_is_uint8 i_2 ==>
          utc_is_uint8 i_3 ==>
          utc_is_uint16 i ==>
          utc_is_uint16 i_1 ==>
          utc_valid_rw t a 1 ==>
          utc_valid_rw t a_1 1 ==>
          utc_valid_rw t a_2 1 ==>
          utc_valid_rw t a_3 1 ==>
          utc_valid_rw t a_4 1 ==>
          utc_valid_rw t a_5 1 ==>
          utc_valid_rw t a_6 1 ==>
          utc_is_uint8 x ==>
          utc_is_uint8 x_1 ==>
          utc_is_uint8 x_2 ==>
          utc_is_uint8 x_3 ==>
          utc_is_uint8 x_4 ==>
          utc_is_uint8 (t_1 a_16) ==>
          utc_valid_rd t a_8 1 ==>
          utc_valid_rd t a_9 1 ==>
          utc_valid_rd t a_11 1 ==>
          utc_valid_rd t a_12 1 ==>
          utc_valid_rd t a_13 1 ==>
          utc_valid_rd t a_14 1 ==>
          utc_valid_rd t a_15 1 ==>
          utc_valid_rd t a_16 1 ==>
          utc_valid_rd t a_10 1 ==>
          utc_separated a 1 a_8 i_1 ==>
          utc_separated a_1 1 a_8 i_1 ==>
          utc_separated a_2 1 a_8 i_1 ==>
          utc_separated a_3 1 a_8 i_1 ==>
          utc_separated a_4 1 a_8 i_1 ==>
          utc_separated a_5 1 a_8 i_1 ==>
          utc_separated a_6 1 a_8 i_1 ==>
          utc_valid_rd t (utc_shift a_7 (2 + i_2)) 1 ==>
          (0 < i_1 ==> utc_valid_rd t a_8 i_1) ==>
          (!i_4 : int.
            let x_5 = t_1 (utc_shift a_7 (2 + i_4)) in
              0 <= i_4 ==>
              i_4 < i_2 ==>
              48 <= x_5 /\ x_5 <= 57) ==>
          48 <= x_4``;
