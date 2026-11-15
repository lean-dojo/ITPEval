(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_loop_inv_not_found_preserved_goal4:
  a search_n loop-invariant preservation verification condition asserting that
  no constant subrange has been found after advancing the search position.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal4 =
  ``let sn_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sn_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let sn_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let sn_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sn_constantrange =
      \mint : (int # int) -> int.
       \a : int # int. \first : int. \last : int. \value : int.
        !j : int.
          first <= j ==>
          j < last ==>
          mint (sn_shift a j) = value
    in
    let sn_hasconstantsubrange =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \value : int.
        ?j : int.
          let endpoint = n + j in
            0 <= j /\
            endpoint <= m /\
            sn_constantrange mint a j endpoint value
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !i_4 : int.
      !a : int # int.
      !t_1 : (int # int) -> int.
      !i i_2 i_3 : int.
      !t : int -> int.
      !i_1 i_5 : int.
        let x = 1 + i_4 in
        let a_1 = sn_shift a i_4 in
        let x_1 = t_1 a_1 in
        let x_2 = t_1 (sn_shift a (i - 1)) in
          0 < i_2 ==>
          i_2 <= i_3 ==>
          i_4 < i_3 ==>
          region (FST a) <= 0 ==>
          i_4 <= 4294967294 ==>
          i <= x ==>
          linked t ==>
          sn_is_uint32 i ==>
          sn_is_uint32 i_1 ==>
          sn_is_uint32 i_2 ==>
          sn_is_uint32 i_3 ==>
          sn_is_uint32 i_4 ==>
          sn_is_sint32 i_5 ==>
          sn_is_uint32 x ==>
          sn_is_sint32 x_1 ==>
          sn_constantrange t_1 a i i_4 i_5 ==>
          ~sn_hasconstantsubrange t_1 a i_4 i_2 i_5 ==>
          sn_valid_rd t (sn_shift a 0) i_3 ==>
          sn_valid_rd t a_1 1 ==>
          sn_is_sint32 x_2 ==>
          (0 < i ==> x_2 <> i_5) ==>
          (x_1 <> i_5 \/
           i_1 = i /\
           i_1 + i_2 <> x /\
           i_1 <= x /\
           i_4 <= 4294967294 + i_1) ==>
          ~sn_hasconstantsubrange t_1 a x i_2 i_5``;
