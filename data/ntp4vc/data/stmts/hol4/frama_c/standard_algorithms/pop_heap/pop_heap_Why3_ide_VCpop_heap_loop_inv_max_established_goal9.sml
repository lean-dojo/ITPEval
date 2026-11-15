(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9:
  establishment of the pop-heap loop's upper-bound invariant from heap order,
  maximum-child, integer-bound, and memory-validity conditions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal9 =
  ``let ph_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ph_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ph_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ph_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ph_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ph_heapparent =
      \j : int. (j - 1) quot 2
    in
    let ph_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (ph_shift a j) <=
          mint (ph_shift a (ph_heapparent j))
    in
    let ph_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (ph_shift a j) <= v
    in
    let ph_heapmaximumchild =
      \mint : (int # int) -> int.
       \a : int # int. \n : int. \p : int. \c : int.
        let left = 1 + 2 * p in
        let selected = mint (ph_shift a c) in
        let right = 2 + 2 * p in
          0 <= p /\
          2 + p <= n /\
          (p <= 2147483646 ==> ph_heapparent c = p) /\
          (2 + left <= n ==> mint (ph_shift a left) <= selected) /\
          (2 + right <= n ==> mint (ph_shift a right) <= selected)
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !to_uint32 : int -> int.
        (!z : int. ph_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          ph_is_uint32 z ==>
          to_uint32 z = z) ==>
        !i : int.
        !t_1 : (int # int) -> int.
        !a : int # int.
        !i_1 : int.
        !t : int -> int.
          let x = i - 1 in
          let x_1 = t_1 (ph_shift a x) in
          let a_1 = ph_shift a 0 in
          let x_2 = t_1 a_1 in
            0 < i ==>
            0 < i_1 ==>
            region (FST a) <= 0 ==>
            x_1 < x_2 ==>
            2 <= i ==>
            linked t ==>
            ph_is_uint32 i ==>
            ph_is_uint32 i_1 ==>
            ph_isheap t_1 a i ==>
            ph_is_sint32 x_2 ==>
            ph_heapmaximumchild t_1 a i 0 i_1 ==>
            ph_valid_rd t a_1 1 ==>
            ph_valid_rw t a_1 i ==>
            ph_is_sint32
              (t_1 (ph_shift a (ph_heapparent 0))) ==>
            ph_is_sint32 x_1 ==>
            ph_valid_rd t (ph_shift a (to_uint32 x)) 1 ==>
            (2 + i_1 <= i ==> ph_heapparent i_1 = 0) ==>
            ph_upperbound t_1 a 0 i x_2``;
