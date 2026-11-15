(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_post_reorder_goal1:
  the push-heap postcondition obligation that the conditional heap reordering
  preserves the multiset of the modeled array segment, under the heap,
  memory-validity, integer-bound, and multiset-count hypotheses. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal1 =
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
        let ph_multisetunchanged =
          \mint0 : (int # int) -> int.
           \mint1 : (int # int) -> int.
           \a : int # int. \m : int. \n : int.
            !v : int.
              ph_is_sint32 v ==>
              l_count mint1 a m n v =
              l_count mint0 a m n v
        in
          !region : int -> int.
          !linked : (int -> int) -> bool.
          !a : int # int.
          !i_1 i_5 i_3 i i_2 i_4 : int.
          !t_4 t_2 t_3 t_1 : (int # int) -> int.
          !t : int -> int.
          !p_1 p : bool.
            let a_1 = ph_shift a 0 in
            let x = i_1 - 1 in
            let a_2 = ph_shift a i_5 in
            let a_3 = ph_shift a (to_uint32 x) in
            let x_1 = t_4 a_2 in
            let a_4 = ph_shift a x in
            let x_2 = t_4 a_4 in
            let a_5 = ph_shift a i_3 in
            let m =
              \q : int # int.
                if q = a_4 then x_1 else t_4 q
            in
            let x_3 = t_2 a_5 in
            let a_6 = ph_shift a i in
              0 < i_1 ==>
              region (FST a) <= 0 ==>
              linked t ==>
              ph_is_uint32 i ==>
              ph_is_uint32 i_1 ==>
              ph_is_uint32 i_2 ==>
              ph_is_uint32 i_3 ==>
              ph_is_uint32 i_4 ==>
              ph_is_uint32 i_5 ==>
              ph_valid_rw t a_1 i_1 ==>
              ph_isheap t_4 a x ==>
              (if 2 <= i_1 then
                 p_1 = F /\
                 ph_heapparent x = i_5 /\
                 ph_valid_rd t a_2 1 /\
                 ph_valid_rd t a_3 1 /\
                 (if x_1 < x_2 then
                    (\q : int # int.
                      if q = a_5 then x_2 else t_2 q) = t_3 /\
                    ph_valid_rw t a_5 1 /\
                    ph_valid_rw t a_3 1 /\
                    (if 0 < i_5 then
                       p = F /\
                       i_3 = i_2 /\
                       i_4 = i_2 /\
                       i_4 = i_3 /\
                       ph_heapparent i_3 = i /\
                       ph_havoc t_1 m a_1 i_1 = t_2 /\
                       0 <= i_3 /\
                       x_3 < x_2 /\
                       2 + i_3 <= i_1 /\
                       ph_isheap t_2 a i_1 /\
                       ph_multisetadd t_2 t_4 a i_1 x_3 /\
                       ph_multisetminus t_2 t_4 a i_1 x_2 /\
                       ph_multisetretainrest
                         t_2 t_4 a i_1 x_2 x_3 /\
                       (i_3 <= 0 \/
                        x_2 <= t_2 a_6 /\
                        ph_valid_rd t a_6 1)
                     else
                       i_5 = i_3 /\ m = t_2)
                  else
                    t_4 = t_3)
               else
                 t_4 = t_3) ==>
              ph_multisetunchanged t_3 t_4 a 0 i_1``;
