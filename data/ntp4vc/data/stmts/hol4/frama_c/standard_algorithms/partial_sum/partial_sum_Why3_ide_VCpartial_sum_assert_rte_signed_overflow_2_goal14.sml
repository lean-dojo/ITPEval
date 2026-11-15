(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sum/partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14:
  the signed 32-bit upper-overflow bound for the next partial-sum addition
  under the stated memory, range, validity, separation, accumulation,
  unchanged-memory, and partial-sum conditions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal14 =
  ``let ps14_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ps14_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ps14_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ps14_valid_rw =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let ps14_valid_rd =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let ps14_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let ps14_update =
      \memory : (int # int) -> int.
       \location : int # int.
       \value : int.
       \query : int # int.
        if query = location then value else memory query
    in
    let ps14_havoc =
      \old_memory : (int # int) -> int.
       \new_memory : (int # int) -> int.
       \start : int # int.
       \length : int.
       \query : int # int.
        if ps14_separated query 1 start length
        then new_memory query
        else old_memory query
    in
    let ps14_p_unchanged =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \start : int # int.
       \lower : int.
       \upper : int.
        !index : int.
          lower <= index ==>
          index < upper ==>
          memory1 (ps14_shift start index) =
            memory0 (ps14_shift start index)
    in
    let ps14_p_partialsum =
      \accumulate :
        ((int # int) -> int) -> (int # int) -> int -> int -> int.
       \memory : (int # int) -> int.
       \input : int # int.
       \n : int.
       \output : int # int.
        !index : int.
          0 <= index ==>
          index < n ==>
          memory (ps14_shift output index) =
            accumulate memory input (1 + index) 0
    in
    let ps14_p_accumulatebounds =
      \accumulate :
        ((int # int) -> int) -> (int # int) -> int -> int -> int.
       \memory : (int # int) -> int.
       \start : int # int.
       \n : int.
       \initial : int.
        !index : int.
          index <= n ==>
          0 <= index ==>
          -2147483648 <= accumulate memory start index initial /\
          accumulate memory start index initial <= 2147483647
    in
    let ps14_uint32_projection =
      \to_uint32 : int -> int.
        (!z : int. ps14_is_uint32 (to_uint32 z)) /\
        (!z : int.
          ps14_is_uint32 z ==> to_uint32 z = z) /\
        (!z : int.
          to_uint32 (to_uint32 z) = to_uint32 z)
    in
    let ps14_accumulate_theory =
      \accumulate :
        ((int # int) -> int) -> (int # int) -> int -> int -> int.
        (!memory : (int # int) -> int.
         !start : int # int.
         !n initial : int.
            ps14_is_sint32
              (accumulate memory start n initial)) /\
        (!n initial : int.
         !memory : (int # int) -> int.
         !start : int # int.
            n <= 0 ==>
            ps14_is_sint32 initial ==>
            accumulate memory start n initial = initial) /\
        (!n initial : int.
         !memory : (int # int) -> int.
         !start : int # int.
            0 < n ==>
            ps14_is_sint32 initial ==>
            memory (ps14_shift start (n - 1)) +
                accumulate memory start (n - 1) initial =
              accumulate memory start n initial) /\
        (!initial : int.
         !memory0 memory1 : (int # int) -> int.
         !start : int # int.
         !n : int.
            ps14_is_sint32 initial ==>
            ps14_p_unchanged memory0 memory1 start 0 n ==>
            accumulate memory1 start n initial =
              accumulate memory0 start n initial)
    in
      !to_uint32 : int -> int.
      !accumulate :
        ((int # int) -> int) -> (int # int) -> int -> int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        ps14_uint32_projection to_uint32 ==>
        ps14_accumulate_theory accumulate ==>
        !a a_1 : int # int.
        !t_2 t_1 : (int # int) -> int.
        !i i_1 : int.
        !t : int -> int.
          let a_2 = ps14_shift a 0 in
          let a_3 = ps14_shift a_1 0 in
          let x = t_2 a_3 in
          let a_4 =
            ps14_havoc
              t_1
              (ps14_update t_2 a_2 x)
              (ps14_shift a 1)
              (i - 1)
          in
          let x_1 = i_1 - 1 in
          let a_5 = a_4 (ps14_shift a x_1) in
          let a_6 = a_4 (ps14_shift a_1 i_1) in
          let a_7 = a_4 (ps14_shift a (to_uint32 x_1)) in
            a_5 = accumulate a_4 a_1 i_1 0 ==>
            0 < i ==>
            0 < i_1 ==>
            i_1 <= i ==>
            i_1 < i ==>
            region (FST a) <= 0 ==>
            region (FST a_1) <= 0 ==>
            linked t ==>
            ps14_is_uint32 i ==>
            ps14_is_uint32 i_1 ==>
            ps14_is_sint32 x ==>
            ps14_valid_rd t a_3 1 ==>
            ps14_valid_rd t a_3 i ==>
            ps14_valid_rw t a_2 1 ==>
            ps14_valid_rw t a_2 i ==>
            ps14_p_accumulatebounds
              accumulate t_2 a_1 (1 + i) 0 ==>
            ps14_separated a_3 i a_2 i ==>
            ps14_is_sint32 a_6 ==>
            ps14_is_sint32 a_5 ==>
            ps14_is_sint32 a_7 ==>
            ps14_p_unchanged a_4 t_2 a_1 0 i ==>
            ps14_p_partialsum accumulate a_4 a_1 i_1 a ==>
            a_6 + a_7 <= 2147483647``;
