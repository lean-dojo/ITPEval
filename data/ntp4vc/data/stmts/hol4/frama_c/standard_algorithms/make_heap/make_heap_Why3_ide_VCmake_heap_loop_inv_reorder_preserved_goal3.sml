(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_loop_inv_reorder_preserved_goal3:
  preservation of the make-heap loop's multiset invariant after two bounded
  memory havoc updates. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal3 =
  ``let mh_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let mh_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let mh_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let mh_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if mh_separated q 1 p n then m1 q else m0 q
    in
    let mh_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let mh_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let mh_unchanged =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint1 (mh_shift a j) = mint0 (mh_shift a j)
    in
    let mh_heapparent =
      \j : int. (j - 1) quot 2
    in
    let mh_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (mh_shift a j) <=
          mint (mh_shift a (mh_heapparent j))
    in
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!n m v : int.
         !mint : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          mh_is_sint32 v ==>
          l_count mint a m n v = 0) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (mh_shift a (n - 1)) = v ==>
          m < n ==>
          mh_is_sint32 v ==>
          1 + l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (mh_shift a (n - 1)) <> v ==>
          m < n ==>
          mh_is_sint32 v ==>
          l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!v m n : int.
         !mint0 mint1 : (int # int) -> int.
         !a : int # int.
          mh_is_sint32 v ==>
          mh_unchanged mint0 mint1 a m n ==>
          l_count mint1 a m n v =
          l_count mint0 a m n v) ==>
        let mh_multisetunchanged =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \m : int. \n : int.
            !v : int.
              mh_is_sint32 v ==>
              l_count mint1 a m n v =
              l_count mint0 a m n v
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !i_1 : int.
          !a : int # int.
          !t_1 t_3 : (int # int) -> int.
          !i : int.
          !t_2 : (int # int) -> int.
          !t : int -> int.
            let x = 1 + i_1 in
            let a_1 = mh_shift a 0 in
            let a_2 = mh_havoc t_1 t_3 a_1 i in
            let a_3 = mh_havoc t_2 a_2 a_1 x in
              0 < i ==>
              0 < i_1 ==>
              i_1 <= i ==>
              i_1 < i ==>
              region (FST a) <= 0 ==>
              i_1 <= 4294967294 ==>
              linked t ==>
              mh_is_uint32 i ==>
              mh_is_uint32 i_1 ==>
              mh_is_uint32 x ==>
              mh_valid_rw t a_1 i ==>
              mh_valid_rw t a_1 x ==>
              mh_isheap a_2 a i_1 ==>
              mh_multisetunchanged a_2 t_3 a 0 x ==>
              mh_unchanged a_2 t_3 a x i ==>
              mh_isheap a_3 a x ==>
              mh_multisetunchanged a_3 a_2 a 0 x ==>
              mh_multisetunchanged a_3 t_3 a 0 (2 + i_1)``;
