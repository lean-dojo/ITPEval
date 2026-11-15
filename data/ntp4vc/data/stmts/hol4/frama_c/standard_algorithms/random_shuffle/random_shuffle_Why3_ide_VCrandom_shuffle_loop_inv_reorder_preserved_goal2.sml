(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/random_shuffle/random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_reorder_preserved_goal2:
  preservation of the random-shuffle loop's multiset invariant after the
  modeled exchange of two array entries. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let rs_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let rs_shift_sint32 =
      \p : int # int. \k : int. rs_shift p k
    in
    let rs_valid_rw =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let rs_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let rs_havoc =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \start : int # int.
       \length : int.
       \query : int # int.
        if rs_separated query 1 start length
        then memory1 query
        else memory0 query
    in
    let rs_update =
      \memory : (int # int) -> int.
       \location : int # int.
       \value : int.
       \query : int # int.
        if query = location then value else memory query
    in
    let rs_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let rs_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let rs_unchanged =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \lower : int.
       \upper : int.
        !index : int.
          lower <= index ==>
          index < upper ==>
          memory1 (rs_shift_sint32 a index) =
            memory0 (rs_shift_sint32 a index)
    in
      !to_uint32 : int -> int.
      !to_sint32 : int -> int.
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!z : int. rs_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          rs_is_uint32 z ==>
          to_uint32 z = z) ==>
        (!z : int. rs_is_sint32 (to_sint32 z)) ==>
        (!z : int.
          rs_is_sint32 z ==>
          to_sint32 z = z) ==>
        (!z : int.
          to_sint32 (to_uint32 z) = to_sint32 z) ==>
        (!n m value : int.
         !memory : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          rs_is_sint32 value ==>
          l_count memory a m n value = 0) ==>
        (!n value m : int.
         !memory : (int # int) -> int.
         !a : int # int.
          memory (rs_shift_sint32 a (n - 1)) = value ==>
          m < n ==>
          rs_is_sint32 value ==>
          1 + l_count memory a m (n - 1) value =
            l_count memory a m n value) ==>
        (!n value m : int.
         !memory : (int # int) -> int.
         !a : int # int.
          memory (rs_shift_sint32 a (n - 1)) <> value ==>
          m < n ==>
          rs_is_sint32 value ==>
          l_count memory a m (n - 1) value =
            l_count memory a m n value) ==>
        (!value m n : int.
         !memory0 memory1 : (int # int) -> int.
         !a : int # int.
          rs_is_sint32 value ==>
          rs_unchanged memory0 memory1 a m n ==>
          l_count memory1 a m n value =
            l_count memory0 a m n value) ==>
        let rs_multisetunchanged =
          \memory0 : (int # int) -> int.
           \memory1 : (int # int) -> int.
           \a : int # int.
           \lower : int.
           \upper : int.
            !value : int.
              rs_is_sint32 value ==>
              l_count memory1 a lower upper value =
                l_count memory0 a lower upper value
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !t_1 t_2 : (int # int) -> int.
          !i_2 i_3 i_1 i : int.
          !t : int -> int.
            let a_1 = rs_shift_sint32 a 0 in
            let a_2 = rs_havoc t_1 t_2 a_1 i_2 in
            let a_3 = rs_shift_sint32 a i_3 in
            let a_4 =
              rs_shift_sint32 a (to_uint32 (1 + i_1))
            in
            let a_5 = a_2 a_3 in
            let a_6 =
              rs_update (rs_update a_2 a_3 i) a_4 a_5
            in
            let a_7 = a_6 a_3 in
            let a_8 = a_2 a_4 in
              a_7 = a_8 ==>
              0 < i_2 ==>
              0 < i_3 ==>
              0 <= i_1 ==>
              i_1 < i_3 ==>
              i_3 <= i_2 ==>
              i_3 < i_2 ==>
              region (FST a) <= 0 ==>
              linked t ==>
              rs_is_uint32 i_1 ==>
              rs_is_uint32 i_2 ==>
              rs_is_uint32 i_3 ==>
              rs_valid_rw t a_1 i_2 ==>
              rs_valid_rw t a_3 1 ==>
              rs_is_sint32 a_5 ==>
              rs_is_sint32 a_8 ==>
              rs_valid_rw t a_4 1 ==>
              rs_is_sint32 a_7 ==>
              rs_unchanged a_2 t_2 a i_3 i_2 ==>
              rs_multisetunchanged a_2 t_2 a 0 i_3 ==>
              rs_multisetunchanged
                a_6 t_2 a 0 (to_uint32 (1 + i_3))``;
