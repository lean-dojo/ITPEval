(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/sort_heap/sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_preserved_goal6:
  preservation of the sort-heap loop's multiset-reordering invariant after
  two bounded memory havoc updates, under the stated heap, maximum-element,
  sorted-suffix, and lower-bound invariants. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal6 =
  ``let sh_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let sh_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let sh_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let sh_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if sh_separated q 1 p n then m1 q else m0 q
    in
    let sh_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let sh_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let sh_unchanged =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint1 (sh_shift a j) = mint0 (sh_shift a j)
    in
    let sh_heapparent =
      \j : int. (j - 1) quot 2
    in
    let sh_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (sh_shift a j) <=
          mint (sh_shift a (sh_heapparent j))
    in
    let sh_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (sh_shift a j) <= v
    in
    let sh_maxelement =
      \mint : (int # int) -> int.
       \a : int # int. \n : int. \max_index : int.
        0 <= max_index /\
        max_index < n /\
        sh_upperbound mint a 0 n
          (mint (sh_shift a max_index))
    in
    let sh_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j k : int.
          k < n ==>
          m <= j ==>
          j < k ==>
          mint (sh_shift a j) <= mint (sh_shift a k)
    in
    let sh_lowerbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          v <= mint (sh_shift a j)
    in
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!n m v : int.
         !mint : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          sh_is_sint32 v ==>
          l_count mint a m n v = 0) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (sh_shift a (n - 1)) = v ==>
          m < n ==>
          sh_is_sint32 v ==>
          1 + l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (sh_shift a (n - 1)) <> v ==>
          m < n ==>
          sh_is_sint32 v ==>
          l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!v m n : int.
         !mint0 mint1 : (int # int) -> int.
         !a : int # int.
          sh_is_sint32 v ==>
          sh_unchanged mint0 mint1 a m n ==>
          l_count mint1 a m n v =
          l_count mint0 a m n v) ==>
        let sh_multisetunchanged =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \m : int. \n : int.
            !v : int.
              sh_is_sint32 v ==>
              l_count mint1 a m n v =
              l_count mint0 a m n v
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !t_1 t_3 : (int # int) -> int.
          !i : int.
          !t_2 : (int # int) -> int.
          !i_1 : int.
          !t : int -> int.
            let a_1 = sh_shift a 0 in
            let a_2 = sh_havoc t_1 t_3 a_1 i in
            let a_3 = sh_havoc t_2 a_2 a_1 i_1 in
            let x = i_1 - 1 in
            let a_4 = a_3 (sh_shift a x) in
            let a_5 = a_2 a_1 in
              a_4 = a_5 ==>
              0 < i_1 ==>
              i_1 <= i ==>
              0 <= i_1 ==>
              region (FST a) <= 0 ==>
              2 <= i_1 ==>
              linked t ==>
              sh_is_uint32 i ==>
              sh_is_uint32 i_1 ==>
              sh_isheap t_3 a i ==>
              sh_is_sint32 (t_3 a_1) ==>
              sh_valid_rw t a_1 i ==>
              sh_is_sint32 a_5 ==>
              sh_isheap a_2 a i_1 ==>
              sh_sorted a_2 a i_1 i ==>
              sh_multisetunchanged a_2 t_3 a 0 i ==>
              sh_lowerbound a_2 a i_1 i a_5 ==>
              sh_is_sint32 (a_3 a_1) ==>
              sh_is_sint32 a_4 ==>
              sh_isheap a_3 a x ==>
              sh_maxelement a_3 a i_1 x ==>
              sh_unchanged a_3 a_2 a i_1 i ==>
              sh_multisetunchanged a_3 a_2 a 0 i_1 ==>
              sh_multisetunchanged a_3 t_3 a 0 i``;
