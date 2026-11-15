(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_retain_preserved_goal16:
  preservation of the push-heap loop's multiset-retain-rest invariant after
  the conditional parent update, under the heap, memory-validity,
  integer-bound, and multiset-count hypotheses. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal16 =
  ``let ph_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let ph_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ph_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ph_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let ph_havoc =
      \m0 : (int # int) -> int.
       \m1 : (int # int) -> int.
       \p : int # int. \n : int. \q : int # int.
        if ph_separated q 1 p n then m1 q else m0 q
    in
    let ph_is_uint32 =
      \z : int. 0 <= z /\ z < 4294967296
    in
    let ph_is_sint32 =
      \z : int. -2147483648 <= z /\ z < 2147483648
    in
    let ph_unchanged =
      \mint0 : (int # int) -> int.
       \mint1 : (int # int) -> int.
       \a : int # int. \m : int. \n : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint1 (ph_shift a j) = mint0 (ph_shift a j)
    in
    let ph_heapparent =
      \j : int. (j - 1) quot 2
    in
    let ph_isheap =
      \mint : (int # int) -> int.
       \a : int # int. \n : int.
        !j : int.
          0 < j ==>
          j < n ==>
          mint (ph_shift a j) <=
          mint (ph_shift a (ph_heapparent j))
    in
      !to_uint32 : int -> int.
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
        (!z : int. ph_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          ph_is_uint32 z ==>
          to_uint32 z = z) ==>
        (!n m v : int.
         !mint : (int # int) -> int.
         !a : int # int.
          n <= m ==>
          ph_is_sint32 v ==>
          l_count mint a m n v = 0) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ph_shift a (n - 1)) = v ==>
          m < n ==>
          ph_is_sint32 v ==>
          1 + l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!n v m : int.
         !mint : (int # int) -> int.
         !a : int # int.
          mint (ph_shift a (n - 1)) <> v ==>
          m < n ==>
          ph_is_sint32 v ==>
          l_count mint a m (n - 1) v =
          l_count mint a m n v) ==>
        (!v m n : int.
         !mint0 mint1 : (int # int) -> int.
         !a : int # int.
          ph_is_sint32 v ==>
          ph_unchanged mint0 mint1 a m n ==>
          l_count mint1 a m n v =
          l_count mint0 a m n v) ==>
        let ph_multisetadd =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \n : int. \v : int.
            1 + l_count mint1 a 0 n v =
            l_count mint0 a 0 n v
        in
        let ph_multisetminus =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \n : int. \v : int.
            1 + l_count mint0 a 0 n v =
            l_count mint1 a 0 n v
        in
        let ph_multisetretain =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \n : int. \v : int.
            l_count mint1 a 0 n v =
            l_count mint0 a 0 n v
        in
        let ph_multisetretainrest =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \n : int. \v : int. \w : int.
            !z : int.
              z <> v ==>
              z <> w ==>
              ph_is_sint32 z ==>
              ph_multisetretain mint0 mint1 a n z
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !i : int.
          !a : int # int.
          !t_2 t_1 : (int # int) -> int.
          !i_1 : int.
          !t_3 : (int # int) -> int.
          !t : int -> int.
            let x = i - 1 in
            let x_1 = ph_heapparent x in
            let a_1 = ph_shift a x_1 in
            let x_2 = t_2 a_1 in
            let a_2 = ph_shift a x in
            let x_3 = t_2 a_2 in
            let m =
              \q : int # int.
                if q = a_2 then x_2 else t_2 q
            in
            let a_3 = ph_shift a 0 in
            let a_4 = ph_havoc t_1 m a_3 i in
            let a_5 = ph_shift a i_1 in
            let a_6 = a_4 a_5 in
            let x_4 = ph_heapparent i_1 in
            let a_7 = ph_shift a x_4 in
            let a_8 = a_4 a_7 in
            let x_5 = t_3 a_7 in
            let a_9 = ph_shift a (to_uint32 x) in
              0 < i ==>
              0 < i_1 ==>
              0 <= i_1 ==>
              region (FST a) <= 0 ==>
              0 < x_1 ==>
              x_2 < x_3 ==>
              a_6 < x_3 ==>
              a_8 < x_3 ==>
              2 <= i ==>
              2 + i_1 <= i ==>
              linked t ==>
              ph_is_uint32 i ==>
              ph_is_uint32 i_1 ==>
              ph_is_uint32 x_4 ==>
              ph_valid_rd t a_5 1 ==>
              ph_valid_rw t a_3 i ==>
              ph_is_uint32 x_1 ==>
              ph_isheap t_2 a x ==>
              ph_is_sint32 x_5 ==>
              ph_valid_rd t a_7 1 ==>
              ph_is_uint32 (ph_heapparent x_1) ==>
              ph_is_sint32 x_3 ==>
              ph_is_sint32 x_2 ==>
              ph_valid_rd t a_9 1 ==>
              ph_valid_rd t a_1 1 ==>
              ph_valid_rw t a_9 1 ==>
              ph_is_sint32 (m a_1) ==>
              ph_is_sint32 a_6 ==>
              ph_is_sint32 a_8 ==>
              ph_isheap a_4 a i ==>
              ph_multisetminus a_4 t_2 a i x_3 ==>
              ph_multisetadd a_4 t_2 a i a_6 ==>
              ph_multisetretainrest a_4 t_2 a i x_3 a_6 ==>
              (if a_6 < a_8 then
                 (\q : int # int.
                   if q = a_5 then a_8 else a_4 q) = t_3 /\
                 ph_valid_rw t a_5 1
               else
                 a_4 = t_3) ==>
              ph_multisetretainrest t_3 t_2 a i x_3 x_5``;
