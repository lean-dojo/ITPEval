(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/is_sorted/is_sorted_Why3_ide_VCis_sorted_post_goal0:
  the result flag of an array sortedness check characterizes the full segment
  sortedness predicate under its memory and loop-state conditions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let is_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let is_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let is_weaklysorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          2 + j <= n ==>
          mint (is_shift a j) <= mint (is_shift a (1 + j))
    in
    let is_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (is_shift a j) <= mint (is_shift a k)
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. is_uint32 (to_uint32 z)) ==>
        (!z : int.
          is_uint32 z ==>
          to_uint32 z = z) ==>
        !i_2 : int.
        !a : int # int.
        !t : int -> int.
        !i i_1 : int.
        !p : bool.
        !t_1 : (int # int) -> int.
          let x = 1 + i_2 in
          let a_1 = is_shift a i_2 in
            region (FST a) <= 0 ==>
            linked t ==>
            is_uint32 i ==>
            is_uint32 i_2 ==>
            is_sint32 i_1 ==>
            is_valid_rd t (is_shift a 0) i ==>
            (if 0 < i then
               p = F /\
               is_weaklysorted t_1 a 0 x /\
               (if 2 + i_2 <= i then
                  i_1 = 0 /\
                  t_1 (is_shift a x) < t_1 a_1 /\
                  i_2 <= 4294967294 /\
                  is_valid_rd t a_1 1 /\
                  is_valid_rd t (is_shift a (to_uint32 x)) 1
                else
                  i_1 = 1)
             else
               i_1 = 1) ==>
            (is_sorted t_1 a 0 i = ~(i_1 = 0))``;
