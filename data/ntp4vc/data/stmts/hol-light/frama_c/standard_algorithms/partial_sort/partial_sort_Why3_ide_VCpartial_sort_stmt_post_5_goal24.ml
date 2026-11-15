(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_5_goal24:
  a partial-sort verification condition asserting preservation of the
  array-prefix multiset after restoring the heap and lower-bound invariants,
  under the stated index, memory-validity, integer-range, heap, bound, swap,
  linkage, and memory-region assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_1 t_5:(int#int)->int.
   !i_2:int.
   !t_2:(int#int)->int.
   !i_1:int.
   !t_3:(int#int)->int.
   !i_3 i:int.
   !t_4:(int#int)->int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let update =
       \(f:(int#int)->int)
        (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_unchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint1 (shift base_addr j) =
               mint0 (shift base_addr j) in
     let p_isheap =
       \(mint:(int#int)->int) (base_addr:int#int) (upper:int).
         !j:int.
           (&0:int) < j
           ==> j < upper
           ==> mint (shift base_addr j) <=
               mint
                 (shift base_addr
                   (cdiv (j - (&1:int)) (&2:int))) in
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let p_upperbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let p_lowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value <= mint (shift base_addr j) in
     let p_maxelement =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (maximum_index:int).
         (&0:int) <= maximum_index /\
         maximum_index < upper /\
         p_upperbound mint base_addr (&0:int) upper
           (mint (shift base_addr maximum_index)) in
     let p_swappedinside =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (first:int) (second:int) (upper:int).
         let first_addr = shift base_addr first in
         let second_addr = shift base_addr second in
         mint1 first_addr = mint0 second_addr /\
         mint1 second_addr = mint0 first_addr /\
         (&0:int) <= first /\
         first < second /\
         second < upper /\
         p_unchanged mint0 mint1 base_addr (&0:int) first /\
         p_unchanged mint0 mint1 base_addr ((&1:int) + first) second /\
         p_unchanged mint0 mint1 base_addr ((&1:int) + second) upper in
     let a_1 = shift a (&0:int) in
     let a_2 = havoc t_1 t_5 a_1 i_2 in
     let a_3 = havoc t_2 a_2 a_1 i_1 in
     let a_4 = havoc t_3 a_3 a_1 i_2 in
     let x = i_2 - (&1:int) in
     let a_5 = shift a x in
     let a_6 = a_4 a_5 in
     let a_7 = a_3 a_1 in
     let a_8 = shift a i_3 in
     let a_9 = a_4 a_8 in
     let a_10 = update (update a_4 a_8 i) a_5 a_9 in
     let a_11 = a_10 a_8 in
     let a_12 = a_3 a_8 in
     let x_1 = (&1:int) + i_3 in
     let a_13 = havoc t_4 a_10 a_1 i_2 in
     let a_14 = a_13 a_1 in
     (!n m value:int.
        !mint:(int#int)->int.
        !base_addr:int#int.
          n <= m
          ==> is_sint32 value
          ==> l_count mint base_addr m n value = (&0:int))
     ==> (!n value m:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              mint (shift base_addr (n - (&1:int))) = value
              ==> m < n
              ==> is_sint32 value
              ==> (&1:int) +
                  l_count mint base_addr m (n - (&1:int)) value =
                  l_count mint base_addr m n value)
     ==> (!n value m:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              ~(mint (shift base_addr (n - (&1:int))) = value)
              ==> m < n
              ==> is_sint32 value
              ==> l_count mint base_addr m (n - (&1:int)) value =
                  l_count mint base_addr m n value)
     ==> (!value m n:int.
            !mint0 mint1:(int#int)->int.
            !base_addr:int#int.
              is_sint32 value
              ==> p_unchanged mint0 mint1 base_addr m n
              ==> l_count mint1 base_addr m n value =
                  l_count mint0 base_addr m n value)
     ==> a_6 = a_7
     ==> a_11 = a_6
     ==> (&0:int) < i_2
     ==> i_2 <= i_1
     ==> i_3 <= i_1
     ==> (&0:int) <= i_2
     ==> i_3 < i_1
     ==> i_2 <= i_3
     ==> region (FST a) <= (&0:int)
     ==> a_12 < a_7
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rw t a_1 i_1
     ==> valid_rw t a_1 i_2
     ==> valid_rw t a_8 (&1:int)
     ==> valid_rw t a_5 (&1:int)
     ==> p_isheap a_2 a i_2
     ==> p_multisetunchanged a_2 t_5 a (&0:int) i_2
     ==> is_sint32 a_7
     ==> is_sint32 a_12
     ==> p_isheap a_3 a i_2
     ==> p_multisetunchanged a_3 t_5 a (&0:int) i_3
     ==> p_unchanged a_3 t_5 a i_3 i_1
     ==> p_upperbound a_3 a (&0:int) i_2 a_7
     ==> p_lowerbound a_3 a i_2 i_3 a_7
     ==> is_sint32 a_9
     ==> is_sint32 a_6
     ==> p_isheap a_4 a x
     ==> is_sint32 a_11
     ==> p_multisetunchanged a_4 t_5 a (&0:int) x_1
     ==> p_multisetunchanged a_4 a_3 a (&0:int) i_2
     ==> p_maxelement a_4 a i_2 x
     ==> p_isheap a_10 a x
     ==> p_multisetunchanged a_10 a_4 a (&0:int) x_1
     ==> p_unchanged a_10 a_4 a x_1 i_1
     ==> p_swappedinside a_10 a_4 a x i_3 x_1
     ==> is_sint32 a_14
     ==> p_isheap a_13 a i_2
     ==> p_multisetunchanged a_13 a_10 a (&0:int) i_2
     ==> p_lowerbound a_13 a i_2 x_1 a_14
     ==> p_multisetunchanged a_13 a_10 a (&0:int) x_1`;;
