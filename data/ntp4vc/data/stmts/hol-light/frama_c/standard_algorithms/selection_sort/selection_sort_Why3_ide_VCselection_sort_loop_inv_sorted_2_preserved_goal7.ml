(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_loop_inv_sorted_2_preserved_goal7:
  a selection-sort loop verification condition asserting that the value at
  the swapped loop position is a lower bound for the remaining array suffix,
  under the stated bounds, sortedness, minimum-element, unchanged-range,
  memory-validity, linkage, multiset, and counting assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_1 t_2:(int#int)->int.
   !i_2 i_3 i_1 i:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
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
       \(f:(int#int)->int) (p:int#int) (value:int) (q:int#int).
         if q = p then value else f q in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_sorted =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     let p_lowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value <= mint (shift base_addr j) in
     let p_strictlowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value < mint (shift base_addr j) in
     let p_minelement =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (min_index:int).
         (&0:int) <= min_index /\
         min_index < upper /\
         p_lowerbound mint base_addr (&0:int) upper
           (mint (shift base_addr min_index)) in
     let p_unchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint1 (shift base_addr j) =
               mint0 (shift base_addr j) in
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let a_1 = shift a (&0:int) in
     let a_2 = havoc t_1 t_2 a_1 i_2 in
     let a_3 = shift a i_3 in
     let a_4 = shift a i_1 in
     let a_5 = a_2 a_3 in
     let a_6 = update (update a_2 a_3 i) a_4 a_5 in
     let a_7 = a_6 a_3 in
     let a_8 = a_2 a_4 in
     let x = (&1:int) + i_3 in
     let x_2 = i_1 - i_3 in
     let x_3 = i_2 - i_3 in
     let a_9 = a_2 (shift a (i_3 - (&1:int))) in
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
     ==> a_7 = a_8
     ==> (&0:int) <= i_1
     ==> i_1 < i_2
     ==> i_3 <= i_1
     ==> i_1 <= i_2
     ==> i_3 <= i_2
     ==> (&0:int) <= i_3
     ==> i_3 < i_2
     ==> region (FST a) <= (&0:int)
     ==> i_3 <= (&4294967294:int)
     ==> i_1 <= (&4294967295:int)
     ==> i_2 <= (&4294967295:int) + i_3
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 x
     ==> is_uint32 x_2
     ==> is_sint32 (t_2 (shift a (--(&1:int))))
     ==> valid_rw t a_1 i_2
     ==> valid_rd t a_3 x_3
     ==> is_sint32 a_8
     ==> is_sint32 a_5
     ==> is_sint32 a_9
     ==> p_sorted a_2 a (&0:int) i_3
     ==> is_sint32 a_7
     ==> p_multisetunchanged a_2 t_2 a (&0:int) i_2
     ==> p_minelement a_2 a_3 x_3 x_2
     ==> p_strictlowerbound a_2 a_3 (&0:int) x_2 a_8
     ==> p_unchanged a_6 a_2 a (&0:int) i_3
     ==> p_unchanged a_6 a_2 a ((&1:int) + i_1) i_2
     ==> p_unchanged a_6 a_2 a x i_1
     ==> ((&0:int) < i_3
          ==> p_lowerbound a_2 a i_3 i_2 a_9)
     ==> p_lowerbound a_6 a x i_2 a_7`;;
