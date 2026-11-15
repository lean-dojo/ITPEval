(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1:
  the post-partition property for partial sort after a conditional havoced
  memory update, under the stated memory-validity, integer-range, heap,
  ordering, multiset, unchanged-region, and bound assumptions. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
  ``let ps_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ps_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
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
    let ps_sorted =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j1 j : int.
          j < n ==>
          m <= j1 ==>
          j1 < j ==>
          mint (ps_shift a j1) <= mint (ps_shift a j)
    in
    let ps_partition =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        0 <= m ==>
        m <= n ==>
        !j1 j : int.
          m <= j ==>
          j < n ==>
          0 <= j1 ==>
          j1 < m ==>
          mint (ps_shift a j1) <= mint (ps_shift a j)
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
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !t_6 t_3 t_5 : (int # int) -> int.
          !i_2 i_1 i : int.
          !t : int -> int.
          !p : bool.
          !t_1 : int -> int.
          !t_2 t_8 t_4 t_7 : (int # int) -> int.
            let a_1 = ps_shift a 0 in
            let x = t_6 a_1 in
            let a_2 = ps_havoc t_3 t_5 a_1 i_2 in
              i_1 <= i ==>
              0 <= i_1 ==>
              region (FST a) <= 0 ==>
              linked t ==>
              ps_is_uint32 i ==>
              ps_is_uint32 i_1 ==>
              ps_is_uint32 i_2 ==>
              ps_is_sint32 (t_5 a_1) ==>
              ps_is_sint32 x ==>
              ps_valid_rw t a_1 i ==>
              (if 0 < i_1 then
                 p = F /\
                 t_1 = t /\
                 ps_havoc t_2 t_8 a_1 i_1 = t_5 /\
                 ps_havoc t_3 t_5 a_1 i = t_6 /\
                 ps_havoc t_4 a_2 a_1 i_1 = t_7 /\
                 i_2 <= i /\
                 i <= i_2 /\
                 i_1 <= i_2 /\
                 ps_sorted t_7 a 0 i_1 /\
                 ps_isheap t_5 a i_1 /\
                 ps_isheap t_6 a i_1 /\
                 ps_multisetunchanged t_5 t_8 a 0 i_1 /\
                 ps_multisetunchanged t_6 t_8 a 0 i_2 /\
                 ps_unchanged t_6 t_8 a i_2 i /\
                 ps_valid_rw t_1 a_1 i_1 /\
                 ps_upperbound t_6 a 0 i_1 x /\
                 ps_lowerbound t_6 a i_1 i_2 x /\
                 ps_multisetunchanged t_7 a_2 a 0 i_1
               else
                 t_8 = t_7) ==>
              ps_partition t_7 a i_1 i``;
