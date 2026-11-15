(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/SortedShift_Why3_ide_VCSortedShift_post_goal0:
  a sortedness property on an integer-indexed memory segment is preserved
  when the base address is shifted to the segment's lower bound and the
  interval is rebased at zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let ss_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ss_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ss_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (ss_shift a j) <= mint (ss_shift a k)
    in
      !region : int -> int.
      !i_1 i : int.
      !a : int # int.
      !t : (int # int) -> int.
        i_1 <= i ==>
        region (FST a) <= 0 ==>
        ss_is_uint32 i ==>
        ss_is_uint32 i_1 ==>
        ss_sorted t a i_1 i ==>
        ss_sorted t (ss_shift a i_1) 0 (i - i_1)``;
