(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_max_goal2:
  the pop-heap postcondition verification condition asserting that the former
  final array position contains a maximum element after the modeled heap and
  memory updates. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory;

val goal2 =
  ``let ph_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
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
    let ph_update =
      \f : (int # int) -> int.
       \p : int # int. \v : int. \q : int # int.
        if q = p then v else f q
    in
    let ph_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
    in
    let ph_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\
        SND p + n <= malloc (FST p)
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
    let ph_upperbound =
      \mint : (int # int) -> int.
       \a : int # int. \m : int. \n : int. \v : int.
        !j : int.
          m <= j ==>
          j < n ==>
          mint (ph_shift a j) <= v
    in
    let ph_maxelement =
      \mint : (int # int) -> int.
       \a : int # int. \n : int. \maximum : int.
        0 <= maximum /\
        maximum < n /\
        ph_upperbound
          mint a 0 n (mint (ph_shift a maximum))
    in
    let ph_heapmaximumchild =
      \mint : (int # int) -> int.
       \a : int # int. \n : int. \p : int. \c : int.
        let left = 1 + 2 * p in
        let selected = mint (ph_shift a c) in
        let right = 2 + 2 * p in
          0 <= p /\
          2 + p <= n /\
          (p <= 2147483646 ==> ph_heapparent c = p) /\
          (2 + left <= n ==>
            mint (ph_shift a left) <= selected) /\
          (2 + right <= n ==>
            mint (ph_shift a right) <= selected)
    in
      !l_count :
        ((int # int) -> int) ->
        (int # int) -> int -> int -> int -> int.
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
        !region : int -> int.
        !linked : (int -> int) -> bool.
        !to_uint32 : int -> int.
        (!z : int. ph_is_uint32 (to_uint32 z)) ==>
        (!z : int.
          ph_is_uint32 z ==>
          to_uint32 z = z) ==>
        !a : int # int.
        !t_4 : (int # int) -> int.
        !i i_1 : int.
        !t_3 : (int # int) -> int.
        !i_3 : int.
        !t : int -> int.
        !i_2 : int.
        !t_5 : (int # int) -> int.
        !p p_1 : bool.
        !t_1 : int -> int.
        !t_2 : (int # int) -> int.
          let a_1 = ph_shift a 0 in
          let x = t_4 a_1 in
          let x_1 = i - 1 in
          let a_2 = ph_shift a x_1 in
          let a_3 = ph_shift a (to_uint32 x_1) in
          let a_4 = ph_shift a i_1 in
          let x_2 = t_3 a_2 in
          let a_5 = ph_shift a i_3 in
            0 < i ==>
            region (FST a) <= 0 ==>
            linked t ==>
            ph_is_uint32 i ==>
            ph_is_uint32 i_1 ==>
            ph_is_uint32 i_2 ==>
            ph_is_uint32 i_3 ==>
            ph_isheap t_4 a i ==>
            ph_is_sint32 x ==>
            ph_valid_rw t a_1 i ==>
            ph_is_sint32 (t_5 a_2) ==>
            (if 2 <= i then
               ph_valid_rd t a_1 1 /\
               ph_valid_rd t a_3 1 /\
               (if t_4 a_2 < x then
                  p = F /\
                  p_1 = F /\
                  t_1 = t /\
                  ph_havoc t_2 t_4 a_1 x_1 = t_3 /\
                  ph_update
                    (ph_update t_3 a_4 x_2) a_2 x = t_5 /\
                  0 < i_2 /\
                  0 <= i_1 /\
                  i_1 < i_3 /\
                  x_2 <
                    t_3 (ph_shift a (ph_heapparent i_1)) /\
                  2 + i_1 <= i /\
                  ph_isheap t_3 a i /\
                  ph_heapmaximumchild t_3 a i i_1 i_3 /\
                  ph_heapmaximumchild t_4 a i 0 i_2 /\
                  ph_valid_rw t_1 a_1 i /\
                  ph_valid_rw t_1 a_4 1 /\
                  ph_upperbound t_3 a 0 i x /\
                  ph_valid_rd t_1 a_3 1 /\
                  ph_valid_rw t_1 a_3 1 /\
                  (2 + i_2 <= i ==>
                    ph_heapparent i_2 = 0) /\
                  (2 + i_3 <= i ==>
                    ph_heapparent i_3 = i_1) /\
                  (i <= 1 + i_3 \/
                   t_3 a_5 <= x_2 /\
                   ph_valid_rd t_1 a_5 1) /\
                  (!v : int.
                    ph_is_sint32 v ==>
                    l_count t_4 a 0 i v +
                      (if t_3 a_4 = v then 1 else 0) =
                    l_count t_3 a 0 i v +
                      (if x = v then 1 else 0))
                else
                  t_5 = t_4)
             else
               t_5 = t_4) ==>
            ph_maxelement t_5 a i x_1``;
