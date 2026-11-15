(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16:
  a search_n no-match postcondition verification condition concluding that the
  returned index equals the no-match result under integer-range, memory, and
  constant-subrange assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal16 =
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
      !to_uint32 : int -> int.
        (!z : int. sn_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          sn_is_uint32 z ==>
          to_uint32 z = z) ==>
        !t_1 : (int # int) -> int.
        !a : int # int.
        !i i_7 i_3 : int.
        !t : int -> int.
        !i_1 i_2 i_4 i_5 i_6 i_8 : int.
          let x = t_1 (sn_shift a (i - 1)) in
          let x_1 = 1 + i_7 in
          let a_1 = sn_shift a i_7 in
          let x_2 = i_3 + to_uint32 x_1 in
            region (FST a) <= 0 ==>
            linked t ==>
            sn_is_uint32 i ==>
            sn_is_uint32 i_1 ==>
            sn_is_uint32 i_2 ==>
            sn_is_uint32 i_3 ==>
            sn_is_uint32 i_4 ==>
            sn_is_uint32 i_5 ==>
            sn_is_uint32 i_6 ==>
            sn_is_uint32 i_7 ==>
            sn_is_sint32 i_8 ==>
            ~sn_hasconstantsubrange t_1 a i_5 i_3 i_8 ==>
            sn_valid_rd t (sn_shift a 0) i_5 ==>
            sn_is_sint32 x ==>
            (if 0 < i_3 then
               if i_3 <= i_5 then
                 i_5 = i_4 /\
                 i_6 = i_4 /\
                 i_6 = i_5 /\
                 i <= x_1 /\
                 sn_constantrange t_1 a i i_7 i_8 /\
                 ~sn_hasconstantsubrange t_1 a i_7 i_3 i_8 /\
                 (if i_7 < i_5 then
                    i + i_3 = x_1 /\
                    i_1 + i_3 = x_1 /\
                    i_2 + i_3 = x_1 /\
                    t_1 a_1 = i_8 /\
                    i_7 < x_2 /\
                    i_7 <= 4294967294 /\
                    x_2 <= 4294967296 + i_7 /\
                    sn_valid_rd t a_1 1
                  else
                    i_5 = i_2) /\
                 (0 < i ==> x <> i_8)
               else
                 i_5 = i_2
             else
               i_2 = 0) ==>
            i_5 = i_2``;
