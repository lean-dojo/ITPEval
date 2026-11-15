(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26:
  the lower-bound call receives a sorted prefix of the shifted array, whose
  length is half the current search interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal26 =
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
    let er_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (er_shift a j) <= mint (er_shift a k)
    in
    let er_strictupperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (er_shift a j) < v
    in
    let er_strictlowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v < mint (er_shift a j)
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. er_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          er_is_uint32 z ==>
          to_uint32 z = z) ==>
        !i_2 i_3 : int.
        !a : int # int.
        !t_1 : (int # int) -> int.
        !i_1 i : int.
        !t : int -> int.
          let x = i_2 - i_3 in
          let x_1 = x quot 2 in
          let x_2 = i_3 + x_1 in
          let a_1 = er_shift_sint32 a x_2 in
          let x_3 = t_1 a_1 in
          let x_4 = i_3 + to_uint32 ((to_uint32 x) quot 2) in
            i_2 <= i_1 ==>
            i_3 <= i_2 ==>
            0 <= i_3 ==>
            i_3 < i_2 ==>
            region (FST a) <= 0 ==>
            0 <= x_1 ==>
            x_3 <= i ==>
            0 <= x_4 ==>
            i <= x_3 ==>
            i_2 <= 4294967295 + i_3 ==>
            x_1 <= 4294967295 ==>
            x_4 <= 4294967295 ==>
            linked t ==>
            er_is_uint32 i_1 ==>
            er_is_uint32 i_2 ==>
            er_is_uint32 i_3 ==>
            er_is_sint32 i ==>
            er_sorted t_1 a 0 i_1 ==>
            er_strictupperbound t_1 a 0 i_3 i ==>
            er_strictlowerbound t_1 a i_2 i_1 i ==>
            er_valid_rd t (er_shift_sint32 a 0) i_1 ==>
            er_is_uint32 x_2 ==>
            er_is_sint32 x_3 ==>
            er_valid_rd t a_1 1 ==>
            er_sorted t_1 (er_shift_sint32 a i_3) 0 x_1``;
