(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/binary_search/binary_search_Why3_ide_VCbinary_search_post_result_goal0:
  the binary-search result flag is nonzero exactly when the target occurs at
  an index in the searched array range. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let bs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let bs_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let bs_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let bs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let bs_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (bs_shift a j) <= mint (bs_shift a k)
    in
    let bs_lowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v <= mint (bs_shift a j)
    in
    let bs_strictupperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (bs_shift a j) < v
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a : int # int.
      !i_2 : int.
      !t_1 : (int # int) -> int.
      !i_1 : int.
      !t : int -> int.
      !i : int.
      !i_3 : int.
        let a_1 = bs_shift a i_2 in
        let x = t_1 a_1 in
          i_2 <= i_1 ==>
          0 <= i_2 ==>
          region (FST a) <= 0 ==>
          linked t ==>
          bs_is_uint32 i_1 ==>
          bs_is_uint32 i_2 ==>
          bs_is_sint32 i ==>
          bs_is_sint32 i_3 ==>
          bs_sorted t_1 a 0 i_1 ==>
          bs_is_sint32 x ==>
          bs_lowerbound t_1 a i_2 i_1 i ==>
          bs_strictupperbound t_1 a 0 i_2 i ==>
          bs_valid_rd t (bs_shift a 0) i_1 ==>
          (if i_2 < i_1 then
             bs_valid_rd t a_1 1 /\
             (if x <= i then i_3 = 1 else i_3 = 0)
           else
             i_3 = 0) ==>
          ((?i_4 : int.
              t_1 (bs_shift a i_4) = i /\
              0 <= i_4 /\
              i_4 < i_1) <=>
           ~(i_3 = 0))``;
