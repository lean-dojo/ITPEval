(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/UpperBoundShift_Why3_ide_VCUpperBoundShift_post_goal0:
  an upper-bound property on an integer-indexed memory segment is preserved
  when the shifted base and zero-based interval are translated back to the
  original base and bounds. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let ubs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ubs_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ubs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ubs_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (ubs_shift a j) <= v
    in
      !i_2 i_1 : int.
      !a : int # int.
      !i : int.
      !t : (int # int) -> int.
      !region : int -> int.
        i_2 <= i_1 ==>
        region (FST a) <= 0 ==>
        ubs_is_uint32 i_1 ==>
        ubs_is_uint32 i_2 ==>
        ubs_is_sint32 i ==>
        ubs_upperbound
          t (ubs_shift a i_2) 0 (i_1 - i_2) i ==>
        ubs_upperbound t a i_2 i_1 i``;
