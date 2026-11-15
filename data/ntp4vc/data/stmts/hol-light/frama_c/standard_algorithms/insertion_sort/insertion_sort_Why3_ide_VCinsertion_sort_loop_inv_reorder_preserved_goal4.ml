(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_reorder_preserved_goal4:
  an insertion-sort loop verification condition stating that the multiset of
  the extended prefix is preserved after rotating two adjacent ranges, under
  the stated bounds, sortedness, memory-validity, and ordering invariants.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !i_2 i_1:int.
   !a:int#int.
   !t_1 t_3:(int#int)->int.
   !i:int.
   !t_2:(int#int)->int.
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
     let p_upperbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let p_strictlowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value < mint (shift base_addr j) in
     let p_equalranges =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int)
        (target:int).
         !j:int.
           (&0:int) <= j
           ==> j < upper - lower
           ==> mint1 (shift (shift base_addr lower) j) =
               mint0 (shift (shift base_addr target) j) in
     let x_1 = i_2 - i_1 in
     let x_2 = (&1:int) + i_2 in
     let a_1 = shift a (&0:int) in
     let a_2 = shift a i_2 in
     let a_3 = shift a i_1 in
     let x_3 = (&1:int) + i_2 - i_1 in
     let a_4 = havoc t_1 t_3 a_1 i in
     let a_5 = a_4 a_2 in
     let a_6 = havoc t_2 a_4 a_3 x_3 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (!n m value:int.
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
     ==> i_2 <= i
     ==> (&0:int) <= i_1
     ==> (&0:int) <= i_2
     ==> i_2 < i
     ==> i_1 <= i_2
     ==> region (FST a) <= (&0:int)
     ==> i_2 <= (&4294967294:int)
     ==> i_2 <= (&4294967295:int) + i_1
     ==> to_uint32 x_1 <= (&4294967294:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 x_2
     ==> valid_rd t a_1 i_2
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rw t a_1 i
     ==> valid_rw t a_3 x_3
     ==> is_sint32 a_5
     ==> p_sorted a_4 a (&0:int) i_2
     ==> p_unchanged a_4 t_3 a i_2 i
     ==> p_multisetunchanged a_4 t_3 a (&0:int) i_2
     ==> p_upperbound a_4 a (&0:int) i_1 a_5
     ==> p_strictlowerbound a_4 a i_1 i_2 a_5
     ==> p_equalranges a_6 a_4 a_3
           (&0:int) x_1 (&1:int)
     ==> p_equalranges a_6 a_4 a_3
           x_1 x_3 (&0:int)
     ==> p_multisetunchanged a_6 t_3 a (&0:int) x_2`;;
