(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_post_sorted_goal0:
  the selection-sort postcondition that a modeled array prefix remains sorted
  after the final memory havoc, under the stated bounds, validity, range,
  sorted-prefix, multiset, and lower-bound assumptions. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal0 =
  ``let sel_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sel_valid_rw =
      \allocation : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\
        0 <= SND p /\
        SND p + n <= allocation (FST p)
    in
    let sel_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let sel_havoc =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \start : int # int.
       \length : int.
       \query : int # int.
        if sel_separated query 1 start length
        then memory1 query
        else memory0 query
    in
    let sel_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let sel_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sel_unchanged =
      \memory0 : (int # int) -> int.
       \memory1 : (int # int) -> int.
       \a : int # int.
       \lower : int.
       \upper : int.
        !index : int.
          lower <= index ==>
          index < upper ==>
          memory1 (sel_shift a index) =
            memory0 (sel_shift a index)
    in
    let sel_sorted =
      \memory : (int # int) -> int.
       \a : int # int.
       \lower : int.
       \upper : int.
        !j k : int.
          k < upper ==>
          lower <= j ==>
          j < k ==>
          memory (sel_shift a j) <=
            memory (sel_shift a k)
    in
    let sel_lowerbound =
      \memory : (int # int) -> int.
       \a : int # int.
       \lower : int.
       \upper : int.
       \value : int.
        !index : int.
          lower <= index ==>
          index < upper ==>
          value <= memory (sel_shift a index)
    in
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!n m value : int.
         !memory : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          sel_is_sint32 value ==>
          l_count memory a m n value = 0) ==>
        (!n value m : int.
         !memory : (int # int) -> int.
         !a : int # int.
          memory (sel_shift a (n - 1)) = value ==>
          m < n ==>
          sel_is_sint32 value ==>
          1 + l_count memory a m (n - 1) value =
            l_count memory a m n value) ==>
        (!n value m : int.
         !memory : (int # int) -> int.
         !a : int # int.
          memory (sel_shift a (n - 1)) <> value ==>
          m < n ==>
          sel_is_sint32 value ==>
          l_count memory a m (n - 1) value =
            l_count memory a m n value) ==>
        (!value m n : int.
         !memory0 memory1 : (int # int) -> int.
         !a : int # int.
          sel_is_sint32 value ==>
          sel_unchanged memory0 memory1 a m n ==>
          l_count memory1 a m n value =
            l_count memory0 a m n value) ==>
        let sel_multisetunchanged =
          \memory0 : (int # int) -> int.
           \memory1 : (int # int) -> int.
           \a : int # int.
           \lower : int.
           \upper : int.
            !value : int.
              sel_is_sint32 value ==>
              l_count memory1 a lower upper value =
                l_count memory0 a lower upper value
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !t_1 t_2 : (int # int) -> int.
          !i i_1 : int.
          !t : int -> int.
            let a_1 = sel_shift a 0 in
            let a_2 = sel_havoc t_1 t_2 a_1 i in
            let a_3 = a_2 (sel_shift a (i_1 - 1)) in
              i_1 <= i ==>
              0 <= i_1 ==>
              i <= i_1 ==>
              region (FST a) <= 0 ==>
              linked t ==>
              sel_is_uint32 i ==>
              sel_is_uint32 i_1 ==>
              sel_is_sint32 (t_2 (sel_shift a (-1))) ==>
              sel_valid_rw t a_1 i ==>
              sel_is_sint32 a_3 ==>
              sel_sorted a_2 a 0 i_1 ==>
              sel_multisetunchanged a_2 t_2 a 0 i ==>
              (0 < i_1 ==>
               sel_lowerbound a_2 a i_1 i a_3) ==>
              sel_sorted
                (sel_havoc t_1 t_2 a_1 i_1)
                a 0 i_1``;
