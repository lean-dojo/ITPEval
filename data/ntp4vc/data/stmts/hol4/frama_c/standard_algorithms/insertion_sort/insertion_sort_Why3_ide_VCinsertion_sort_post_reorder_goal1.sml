(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_post_reorder_goal1:
  the insertion-sort postcondition obligation that a memory reordering step
  preserves the multiset of a sorted prefix. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
  ``let ins_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
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
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
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
          !a : int # int.
          !t_1 t_2 : (int # int) -> int.
          !i i_1 : int.
          !t : int -> int.
            let a_1 = ins_shift a 0 in
            let a_2 = ins_havoc t_1 t_2 a_1 i in
              i_1 <= i ==>
              0 <= i_1 ==>
              i <= i_1 ==>
              region (FST a) <= 0 ==>
              linked t ==>
              ins_is_uint32 i ==>
              ins_is_uint32 i_1 ==>
              ins_valid_rw t a_1 i ==>
              ins_sorted a_2 a 0 i_1 ==>
              ins_unchanged a_2 t_2 a i_1 i ==>
              ins_multisetunchanged a_2 t_2 a 0 i_1 ==>
              ins_multisetunchanged
                (ins_havoc t_1 t_2 a_1 i_1) t_2 a 0 i_1``;
