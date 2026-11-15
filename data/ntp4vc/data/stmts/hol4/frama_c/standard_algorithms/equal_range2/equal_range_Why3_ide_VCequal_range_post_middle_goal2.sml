(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_middle_goal2:
  the middle segment returned by an equal-range search is a constant range
  containing the selected value. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
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
    let er_constantrange =
      \mint : (int # int) -> int.
       \a : int # int. \first : int. \last : int. \v : int.
        !j : int.
          first <= j ==>
          j < last ==>
          mint (er_shift a j) = v
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. er_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          er_is_uint32 z ==>
          to_uint32 z = z) ==>
        !s : int # int.
        !i_8 i_10 : int.
        !a : int # int.
        !t_1 : (int # int) -> int.
        !i_7 i_11 : int.
        !t : int -> int.
        !i_1 i_2 i_3 i_4 i_5 i_6 i_9 i : int.
        !p_1 p_2 p_3 p : bool.
          let x = FST s in
          let x_2 = i_8 - i_10 in
          let x_3 = x_2 quot 2 in
          let x_4 = i_10 + x_3 in
          let x_5 = SND s in
          let a_1 = er_shift_sint32 a x_4 in
          let x_6 = t_1 a_1 in
          let x_7 = i_10 + to_uint32 ((to_uint32 x_2) quot 2) in
          let a_2 = er_shift_sint32 a i_10 in
          let a_3 = er_shift_sint32 a (1 + i_10 + x_3) in
          let x_9 = i_8 - 1 - i_10 - x_3 in
          let x_10 = x - i_10 in
          let x_11 = x_5 - 1 - i_10 - x_3 in
            i_8 <= i_7 ==>
            i_11 <= i_8 ==>
            0 <= i_11 ==>
            region (FST a) <= 0 ==>
            er_size_pair_ok s ==>
            linked t ==>
            er_is_uint32 i_1 ==>
            er_is_uint32 i_2 ==>
            er_is_uint32 i_3 ==>
            er_is_uint32 i_4 ==>
            er_is_uint32 i_5 ==>
            er_is_uint32 i_6 ==>
            er_is_uint32 i_7 ==>
            er_is_uint32 i_8 ==>
            er_is_uint32 i_9 ==>
            er_is_uint32 i_10 ==>
            er_is_uint32 i_11 ==>
            er_is_sint32 i ==>
            er_sorted t_1 a 0 i_7 ==>
            er_strictupperbound t_1 a 0 i_11 i ==>
            er_strictlowerbound t_1 a i_8 i_7 i ==>
            er_valid_rd t (er_shift_sint32 a 0) i_7 ==>
            (if i_11 < i_8 then
               p_1 = F /\
               p_2 = F /\
               p_3 = F /\
               i_2 = i_1 /\
               i_5 = i_4 /\
               i_10 = i_9 /\
               i_11 = i_10 /\
               x = i_3 + i_10 /\
               x = i_6 + i_10 /\
               x_4 = i_4 /\
               x_4 = i_5 /\
               x_5 = 1 + i_1 + i_10 + x_3 /\
               x_5 = 1 + i_2 + i_10 + x_3 /\
               x_5 <= i_8 /\
               0 <= x /\
               i_10 <= x /\
               0 <= x_5 /\
               0 <= x_3 /\
               x_4 < i_8 /\
               x <= x_4 /\
               x_4 < x_5 /\
               x_6 <= i /\
               0 <= x_7 /\
               i <= x_6 /\
               x <= 4294967295 /\
               x_5 <= 4294967295 /\
               i_8 <= 4294967295 + i_10 /\
               x_3 <= 4294967295 /\
               x_4 <= 4294967294 /\
               i_8 <= 4294967296 + i_10 + x_3 /\
               x_7 <= 4294967295 /\
               er_valid_rd t a_2 x_3 /\
               er_sorted t_1 a_2 0 x_3 /\
               er_valid_rd t a_1 1 /\
               er_valid_rd t a_3 x_9 /\
               er_sorted t_1 a_3 0 x_9 /\
               er_strictupperbound t_1 a_2 0 x_10 x_6 /\
               er_strictlowerbound t_1 a_3 x_11 x_9 x_6 /\
               er_lowerbound t_1 a_2 x_10 x_3 x_6 /\
               er_upperbound t_1 a_3 0 x_11 x_6
             else
               p = F /\ x = i_11 /\ x_5 = x) ==>
            er_constantrange t_1 a x x_5 i``;
