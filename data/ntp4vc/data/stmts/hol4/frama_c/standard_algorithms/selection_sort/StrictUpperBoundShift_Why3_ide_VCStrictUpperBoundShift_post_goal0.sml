(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/StrictUpperBoundShift_Why3_ide_VCStrictUpperBoundShift_post_goal0:
  a strict upper-bound property on an integer-indexed memory segment is
  preserved when the shifted base and zero-based interval are translated back
  to the original base and bounds. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let subs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let subs_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let subs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let subs_strictupperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (subs_shift a j) < v
    in
      !i_2 i_1 : int.
      !a : int # int.
      !i : int.
      !t : (int # int) -> int.
      !region : int -> int.
        i_2 <= i_1 ==>
        region (FST a) <= 0 ==>
        subs_is_uint32 i_1 ==>
        subs_is_uint32 i_2 ==>
        subs_is_sint32 i ==>
        subs_strictupperbound
          t (subs_shift a i_2) 0 (i_1 - i_2) i ==>
        subs_strictupperbound t a i_2 i_1 i``;
