(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_unchanged_preserved_goal8:
  preservation of the insertion-sort loop's unchanged-suffix invariant after
  a memory shifting step. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal8 =
  ``let ins_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ins_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ins_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ins_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ins_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if ins_separated q 1 p n then m1 q else m0 q
    in
    let ins_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ins_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ins_unchanged =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint1 (ins_shift a j) = mint0 (ins_shift a j)
    in
    let ins_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (ins_shift a j) <= mint (ins_shift a k)
    in
    let ins_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (ins_shift a j) <= v
    in
    let ins_strictlowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v < mint (ins_shift a j)
    in
    let ins_equalranges =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \p : int.
        !j : int.
          0 <= j ==>
          j < n - m ==>
          mint1 (ins_shift (ins_shift a m) j) =
          mint0 (ins_shift (ins_shift a p) j)
    in
      !to_uint32 : int -> int.
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!z : int. ins_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          ins_is_uint32 z ==>
          to_uint32 z = z) ==>
        (!n m v : int.
         !mint : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          ins_is_sint32 v ==>
          l_count mint a m n v = 0) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ins_shift a (n - 1)) = v ==>
          m < n ==>
          ins_is_sint32 v ==>
          1 + l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ins_shift a (n - 1)) <> v ==>
          m < n ==>
          ins_is_sint32 v ==>
          l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!v m n : int.
         !mint0 mint1 : (int # int) -> int.
         !a : int # int.
          ins_is_sint32 v ==>
          ins_unchanged mint0 mint1 a m n ==>
          l_count mint1 a m n v =
          l_count mint0 a m n v) ==>
        let ins_multisetunchanged =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \m : int. \n : int.
            !v : int.
              ins_is_sint32 v ==>
              l_count mint1 a m n v =
              l_count mint0 a m n v
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !i_2 i_1 : int.
          !a : int # int.
          !t_1 t_3 : (int # int) -> int.
          !i : int.
          !t_2 : (int # int) -> int.
          !t : int -> int.
            let x_1 = i_2 - i_1 in
            let x_2 = 1 + i_2 in
            let a_1 = ins_shift a 0 in
            let a_2 = ins_shift a i_2 in
            let a_3 = ins_shift a i_1 in
            let x_3 = 1 + i_2 - i_1 in
            let a_4 = ins_havoc t_1 t_3 a_1 i in
            let a_5 = a_4 a_2 in
            let a_6 = ins_havoc t_2 a_4 a_3 x_3 in
              i_2 <= i ==>
              0 <= i_1 ==>
              0 <= i_2 ==>
              i_2 < i ==>
              i_1 <= i_2 ==>
              region (FST a) <= 0 ==>
              i_2 <= 4294967294 ==>
              i_2 <= 4294967295 + i_1 ==>
              to_uint32 x_1 <= 4294967294 ==>
              linked t ==>
              ins_is_uint32 i ==>
              ins_is_uint32 i_1 ==>
              ins_is_uint32 i_2 ==>
              ins_is_uint32 x_2 ==>
              ins_valid_rd t a_1 i_2 ==>
              ins_valid_rd t a_2 1 ==>
              ins_valid_rw t a_1 i ==>
              ins_valid_rw t a_3 x_3 ==>
              ins_is_sint32 a_5 ==>
              ins_sorted a_4 a 0 i_2 ==>
              ins_unchanged a_4 t_3 a i_2 i ==>
              ins_multisetunchanged a_4 t_3 a 0 i_2 ==>
              ins_upperbound a_4 a 0 i_1 a_5 ==>
              ins_strictlowerbound a_4 a i_1 i_2 a_5 ==>
              ins_equalranges a_6 a_4 a_3 0 x_1 1 ==>
              ins_equalranges a_6 a_4 a_3 x_1 x_3 0 ==>
              ins_unchanged a_6 t_3 a x_2 i``;
