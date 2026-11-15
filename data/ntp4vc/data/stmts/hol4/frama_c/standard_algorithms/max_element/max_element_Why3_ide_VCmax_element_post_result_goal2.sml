(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/max_element/max_element_Why3_ide_VCmax_element_post_result_goal2:
  a maximum-element postcondition verification condition asserting that an
  unsigned 32-bit index is nonnegative under the modeled memory assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let me_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let me_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let me_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !i : int.
      !a : int # int.
      !t : int -> int.
        i <= 0 ==>
        region (FST a) <= 0 ==>
        linked t ==>
        me_is_uint32 i ==>
        me_valid_rd t (me_shift a 0) i ==>
        0 <= i``;
