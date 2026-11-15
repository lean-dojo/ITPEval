(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_left_goal1:
  the established left segment of an equal-range search is strictly below the
  selected midpoint value. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
  ``let er_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let er_shift_sint32 =
      \p : int # int. \k : int. er_shift p k
    in
    let er_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let er_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let er_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let er_size_pair_ok =
      \s : int # int. er_is_uint32 (FST s) /\ er_is_uint32 (SND s)
    in
    let er_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (er_shift a j) <= mint (er_shift a k)
    in
    let er_lowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v <= mint (er_shift a j)
    in
    let er_strictlowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v < mint (er_shift a j)
    in
    let er_strictupperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (er_shift a j) < v
    in
    let er_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (er_shift a j) <= v
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. er_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          er_is_uint32 z ==>
          to_uint32 z = z) ==>
        !s : int # int.
        !i_1 i_3 : int.
        !a : int # int.
        !t_1 : (int # int) -> int.
        !i_2 i : int.
        !t : int -> int.
          let x = SND s in
          let x_1 = FST s in
          let x_2 = i_1 + i_3 in
          let x_3 = -x_1 in
          let x_4 = i_1 + i_3 - x_1 in
          let x_5 = x_4 quot 2 in
          let x_6 = x_1 + x_5 in
          let x_7 = x_1 + to_uint32 ((to_uint32 x_4) quot 2) in
          let x_8 = -i_1 in
          let x_9 = x_1 + x_5 - i_1 in
          let a_1 = er_shift_sint32 a x_9 in
          let x_10 = t_1 a_1 in
          let x_11 = x_1 - i_1 in
          let a_2 = er_shift_sint32 a x_11 in
          let x_12 = 1 + x_1 + x_5 - i_1 in
          let x_13 = -x_5 in
          let x_14 = i_1 + x - 1 - x_1 - x_5 in
          let a_3 = er_shift_sint32 a x_12 in
          let x_15 = i_1 + i_3 - 1 - x_1 - x_5 in
            0 <= i_1 ==>
            i_3 <= i_2 ==>
            x <= i_3 ==>
            0 <= x_1 ==>
            i_1 <= x_1 ==>
            0 <= x ==>
            x_1 < x_2 ==>
            region (FST a) <= 0 ==>
            0 <= x_5 ==>
            i_1 <= x_5 ==>
            x_6 < x_2 ==>
            x_6 < i_1 + x ==>
            i_1 <= x_7 ==>
            x_10 <= i ==>
            i <= x_10 ==>
            x_1 <= 4294967295 ==>
            x <= 4294967295 ==>
            x_2 <= 4294967295 + x_1 ==>
            x_5 <= 4294967295 ==>
            x_6 <= 4294967294 + i_1 ==>
            x_2 <= 4294967296 + x_1 + x_5 ==>
            x_7 <= 4294967295 + i_1 ==>
            er_size_pair_ok s ==>
            linked t ==>
            er_is_uint32 i_1 ==>
            er_is_uint32 i_2 ==>
            er_is_uint32 i_3 ==>
            er_is_sint32 i ==>
            er_is_uint32 x_1 ==>
            er_is_uint32 x ==>
            er_sorted t_1 a 0 i_2 ==>
            er_is_uint32 x_11 ==>
            er_strictlowerbound t_1 a i_3 i_2 i ==>
            er_valid_rd t (er_shift_sint32 a 0) i_2 ==>
            er_strictupperbound t_1 a 0 x_11 i ==>
            er_valid_rd t a_2 x_5 ==>
            er_sorted t_1 a_2 0 x_5 ==>
            er_is_uint32 x_9 ==>
            er_is_uint32 x_12 ==>
            er_is_uint32 x_14 ==>
            er_is_sint32 x_10 ==>
            er_valid_rd t a_1 1 ==>
            er_valid_rd t a_3 x_15 ==>
            er_sorted t_1 a_3 0 x_15 ==>
            er_strictupperbound t_1 a_2 0 i_1 x_10 ==>
            er_strictlowerbound t_1 a_3 x_14 x_15 x_10 ==>
            er_lowerbound t_1 a_2 i_1 x_5 x_10 ==>
            er_upperbound t_1 a_3 0 x_14 x_10 ==>
            er_strictupperbound t_1 a 0 x_1 x_10``;
