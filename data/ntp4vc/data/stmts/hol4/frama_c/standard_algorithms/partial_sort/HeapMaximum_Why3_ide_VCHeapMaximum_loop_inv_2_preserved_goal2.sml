(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2:
  preservation of an upper-bound loop invariant for a heap traversal, under
  the stated integer bounds, uint32 conditions, and heap-order assumption.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let hm_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let hm_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let hm_heapparent =
      \j : int. (j - 1) quot 2
    in
    let hm_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (hm_shift a j) <=
          mint (hm_shift a (hm_heapparent j))
    in
      !region : int -> int.
      !t : (int # int) -> int.
      !a : int # int.
      !i i_1 i_2 : int.
        let x = t (hm_shift a 0)
        in
          0 < i ==>
          i_1 <= i ==>
          0 <= i_1 ==>
          i_1 < i ==>
          i_2 <= i_1 ==>
          0 <= i_2 ==>
          region (FST a) <= 0 ==>
          i_1 <= 4294967294 ==>
          hm_is_uint32 i ==>
          hm_is_uint32 i_1 ==>
          hm_is_uint32 i_2 ==>
          hm_isheap t a i ==>
          hm_is_uint32 (1 + i_1) ==>
          (!i_3 : int.
            0 <= i_3 ==>
            i_3 < i_1 ==>
            t (hm_shift a i_3) <= x) ==>
          t (hm_shift a i_2) <= x``;
