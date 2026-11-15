(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/sort_heap/sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_preserved_goal6:
  a heap-sort loop verification condition asserting preservation of the
  multiset through two memory updates, under the stated index bounds, heap,
  sorted-suffix, lower-bound, maximum-element, unchanged-range,
  memory-validity, integer-range, and linkage invariants.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_1 t_3:(int#int)->int.
   !i:int.
   !t_2:(int#int)->int.
   !i_1:int.
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
     let l_heapparent =
       \j:int. cdiv (j - (&1:int)) (&2:int) in
     let p_isheap =
       \(mint:(int#int)->int) (base_addr:int#int) (upper:int).
         !j:int.
           (&0:int) < j
           ==> j < upper
           ==> mint (shift base_addr j) <=
               mint (shift base_addr (l_heapparent j)) in
     let p_sorted =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let p_lowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value <= mint (shift base_addr j) in
     let p_upperbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let p_maxelement =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (maximum:int).
         (&0:int) <= maximum /\
         maximum < upper /\
         p_upperbound mint base_addr (&0:int) upper
           (mint (shift base_addr maximum)) in
     let a_1 = shift a (&0:int) in
     let a_2 = havoc t_1 t_3 a_1 i in
     let a_3 = havoc t_2 a_2 a_1 i_1 in
     let x = i_1 - (&1:int) in
     let a_4 = a_3 (shift a x) in
     let a_5 = a_2 a_1 in
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
     ==> a_4 = a_5
     ==> (&0:int) < i_1
     ==> i_1 <= i
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> (&2:int) <= i_1
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> p_isheap t_3 a i
     ==> is_sint32 (t_3 a_1)
     ==> valid_rw t a_1 i
     ==> is_sint32 a_5
     ==> p_isheap a_2 a i_1
     ==> p_sorted a_2 a i_1 i
     ==> p_multisetunchanged a_2 t_3 a (&0:int) i
     ==> p_lowerbound a_2 a i_1 i a_5
     ==> is_sint32 (a_3 a_1)
     ==> is_sint32 a_4
     ==> p_isheap a_3 a x
     ==> p_maxelement a_3 a i_1 x
     ==> p_unchanged a_3 a_2 a i_1 i
     ==> p_multisetunchanged a_3 a_2 a (&0:int) i_1
     ==> p_multisetunchanged a_3 t_3 a (&0:int) i`;;
