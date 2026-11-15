(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/reverse/reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7:
  preservation of the right-hand reverse-loop invariant after the modeled
  exchange of two array entries, under the stated integer-range, allocation,
  and unchanged/reversed-segment conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7 =
  ``let rv_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let rv_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let rv_havoc =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \start : int # int.
       \length : int.
       \query : int # int.
        if rv_separated query 1 start length
        then memory1 query
        else memory0 query
    in
    let rv_update =
      \memory : (int # int) -> int.
       \location : int # int.
       \value : int.
       \query : int # int.
        if query = location then value else memory query
    in
    let rv_valid_rw =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let rv_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let rv_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let rv_p_reverse_1 =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \n : int.
       \b : int # int.
        !j : int.
          0 <= j ==>
          j < n ==>
          memory0 (rv_shift b (n - 1 - j)) =
            memory1 (rv_shift a j)
    in
    let rv_p_reverse_2 =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \m : int.
       \n : int.
       \b : int # int.
       \p : int.
        rv_p_reverse_1
          memory0 memory1
          (rv_shift a m) (n - m) (rv_shift b p)
    in
    let rv_p_reverse_4 =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \m : int.
       \n : int.
       \p : int.
        rv_p_reverse_2 memory0 memory1 a m n a p
    in
    let rv_p_unchanged_1 =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \m : int.
       \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          memory1 (rv_shift a j) = memory0 (rv_shift a j)
    in
    let rv_cint32_context =
      \to_uint32 : int -> int.
       \to_sint32 : int -> int.
        (!z : int. rv_is_uint32 (to_uint32 z)) /\
        (!z : int. rv_is_sint32 (to_sint32 z)) /\
        (!z : int.
          rv_is_uint32 z ==> to_uint32 z = z) /\
        (!z : int.
          rv_is_sint32 z ==> to_sint32 z = z) /\
        (!z : int.
          to_uint32 (to_uint32 z) = to_uint32 z)
        /\
        (!z : int.
          to_sint32 (to_sint32 z) = to_sint32 z)
        /\
        (!z : int.
          to_sint32 (to_uint32 z) = to_sint32 z)
    in
      !to_uint32 : int -> int.
      !to_sint32 : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        rv_cint32_context to_uint32 to_sint32 ==>
        !a : int # int.
        !t_1 t_2 : (int # int) -> int.
        !i_1 i_2 i : int.
        !t : int -> int.
          let a_1 = rv_shift a 0 in
          let a_2 = rv_havoc t_1 t_2 a_1 i_1 in
          let x_1 = i_1 - 1 - i_2 in
          let a_3 = rv_shift a x_1 in
          let a_4 = rv_shift a i_2 in
          let a_5 = a_2 a_3 in
          let a_6 =
            rv_update (rv_update a_2 a_3 i) a_4 a_5
          in
          let a_7 = a_6 a_3 in
          let a_8 = a_2 a_4 in
          let x_2 = i_1 quot 2 in
          let x_3 = to_uint32 (i_1 - 1) in
          let x_4 = i_1 - i_2 in
            a_7 = a_8 ==>
            0 < i_1 ==>
            0 <= i_2 ==>
            i_2 < x_2 ==>
            i_2 <= x_2 ==>
            region (FST a) <= 0 ==>
            i_2 + x_2 <= i_1 ==>
            i_2 <= x_3 ==>
            i_2 <= 4294967294 ==>
            x_3 <= 4294967295 + i_2 ==>
            linked t ==>
            rv_is_uint32 i_1 ==>
            rv_is_uint32 i_2 ==>
            rv_is_uint32 x_2 ==>
            rv_is_uint32 (1 + i_2) ==>
            rv_valid_rw t a_1 i_1 ==>
            rv_valid_rw t a_4 1 ==>
            rv_is_sint32 a_8 ==>
            rv_is_sint32 a_5 ==>
            rv_valid_rw t a_3 1 ==>
            rv_is_sint32 a_7 ==>
            rv_p_unchanged_1 a_2 t_2 a i_2 x_4 ==>
            rv_p_reverse_4 a_2 t_2 a 0 i_2 x_4 ==>
            rv_p_reverse_4 a_2 t_2 a x_4 i_1 0 ==>
            rv_p_reverse_4 a_6 t_2 a x_1 i_1 0``;
