(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_goal25:
  preservation of the multiset of the final partial-sort prefix after the
  havoced heap update, under the stated memory, integer-range, heap,
  unchanged-region, ordering, maximum-element, and multiset assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal25 =
  ``let ps_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ps_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ps_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ps_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ps_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if ps_separated q 1 p n then m1 q else m0 q
    in
    let ps_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ps_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ps_unchanged =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint1 (ps_shift a j) = mint0 (ps_shift a j)
    in
    let ps_heapparent =
      \j : int. (j - 1) quot 2
    in
    let ps_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (ps_shift a j) <=
          mint (ps_shift a (ps_heapparent j))
    in
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!n m v : int.
         !mint : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          ps_is_sint32 v ==>
          l_count mint a m n v = 0) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ps_shift a (n - 1)) = v ==>
          m < n ==>
          ps_is_sint32 v ==>
          1 + l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ps_shift a (n - 1)) <> v ==>
          m < n ==>
          ps_is_sint32 v ==>
          l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!v m n : int.
         !mint0 mint1 : (int # int) -> int.
         !a : int # int.
          ps_is_sint32 v ==>
          ps_unchanged mint0 mint1 a m n ==>
          l_count mint1 a m n v =
          l_count mint0 a m n v) ==>
        let ps_multisetunchanged =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \m : int. \n : int.
            !v : int.
              ps_is_sint32 v ==>
              l_count mint1 a m n v =
              l_count mint0 a m n v
        in
        let ps_upperbound =
          \mint : (int # int) -> int.
           \a : int # int. \m : int. \n : int. \v : int.
            !j : int.
              m <= j ==>
              j < n ==>
              mint (ps_shift a j) <= v
        in
        let ps_lowerbound =
          \mint : (int # int) -> int.
           \a : int # int. \m : int. \n : int. \v : int.
            !j : int.
              m <= j ==>
              j < n ==>
              v <= mint (ps_shift a j)
        in
        let ps_maxelement =
          \mint : (int # int) -> int.
           \a : int # int. \n : int. \max_index : int.
            0 <= max_index /\ max_index < n /\
            ps_upperbound mint a 0 n
              (mint (ps_shift a max_index))
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !t_1 t_4 : (int # int) -> int.
          !i_1 : int.
          !t_2 : (int # int) -> int.
          !i : int.
          !t_3 : (int # int) -> int.
          !i_2 : int.
          !t : int -> int.
            let a_1 = ps_shift a 0 in
            let a_2 = ps_havoc t_1 t_4 a_1 i_1 in
            let a_3 = ps_havoc t_2 a_2 a_1 i in
            let a_4 = ps_havoc t_3 a_3 a_1 i_1 in
            let x = i_1 - 1 in
            let a_5 = a_4 (ps_shift a x) in
            let a_6 = a_3 a_1 in
            let a_7 = ps_shift a i_2 in
            let a_8 = a_3 a_7 in
              a_5 = a_6 ==>
              0 < i_1 ==>
              i_1 <= i ==>
              i_2 <= i ==>
              0 <= i_1 ==>
              i_2 < i ==>
              i_1 <= i_2 ==>
              region (FST a) <= 0 ==>
              a_8 < a_6 ==>
              linked t ==>
              ps_is_uint32 i ==>
              ps_is_uint32 i_1 ==>
              ps_is_uint32 i_2 ==>
              ps_valid_rd t a_1 1 ==>
              ps_valid_rd t a_7 1 ==>
              ps_valid_rw t a_1 i ==>
              ps_valid_rw t a_1 i_1 ==>
              ps_isheap a_2 a i_1 ==>
              ps_multisetunchanged a_2 t_4 a 0 i_1 ==>
              ps_is_sint32 a_6 ==>
              ps_is_sint32 a_8 ==>
              ps_isheap a_3 a i_1 ==>
              ps_multisetunchanged a_3 t_4 a 0 i_2 ==>
              ps_unchanged a_3 t_4 a i_2 i ==>
              ps_upperbound a_3 a 0 i_1 a_6 ==>
              ps_lowerbound a_3 a i_1 i_2 a_6 ==>
              ps_is_sint32 a_5 ==>
              ps_isheap a_4 a x ==>
              ps_multisetunchanged a_4 a_3 a 0 i_1 ==>
              ps_maxelement a_4 a i_1 x ==>
              ps_multisetunchanged a_4 t_4 a 0 (1 + i_2)``;
