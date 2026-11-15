(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/StrictLowerBoundShift_Why3_ide_VCStrictLowerBoundShift_post_goal0:
  a strict lower-bound property on an integer-indexed memory segment is
  preserved when its base address and interval bounds are shifted together.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let slbs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let slbs_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let slbs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let slbs_strictlowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v < mint (slbs_shift a j)
    in
      !region : int -> int.
      !i_1 i_3 : int.
      !a : int # int.
      !i_2 i : int.
      !t : (int # int) -> int.
        let x = i_1 + i_3 in
          region (FST a) <= 0 ==>
          x <= 4294967295 ==>
          slbs_is_uint32 i_1 ==>
          slbs_is_uint32 i_2 ==>
          slbs_is_uint32 i_3 ==>
          slbs_is_sint32 i ==>
          slbs_strictlowerbound t (slbs_shift a i_3) i_2 i_1 i ==>
          slbs_strictlowerbound t a (i_2 + i_3) x i``;
