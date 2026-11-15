(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/reverse/reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7:
  a reverse-loop verification condition asserting preservation of the
  right-hand reversal invariant after swapping the current symmetric array
  elements, under the stated bounds, memory-validity, integer-range, linkage,
  unchanged-range, and reversal invariants. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !a:int#int.
   !t_1 t_2:(int#int)->int.
   !i_1 i_2 i:int.
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
     let p_reverse_1 =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (left_addr:int#int) (length:int) (right_addr:int#int).
         !j:int.
           (&0:int) <= j
           ==> j < length
           ==> mint0
                 (shift right_addr (length - (&1:int) - j)) =
               mint1 (shift left_addr j) in
     let p_reverse_2 =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int)
        (right_addr:int#int) (target:int).
         p_reverse_1 mint0 mint1
           (shift base_addr lower) (upper - lower)
           (shift right_addr target) in
     let p_reverse_4 =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int) (target:int).
         p_reverse_2 mint0 mint1 base_addr lower upper
           base_addr target in
     let a_1 = shift a (&0:int) in
     let a_2 = havoc t_1 t_2 a_1 i_1 in
     let x_1 = i_1 - (&1:int) - i_2 in
     let a_3 = shift a x_1 in
     let a_4 = shift a i_2 in
     let a_5 = a_2 a_3 in
     let a_6 =
       \(q:int#int).
         if q = a_4 then a_5
         else if q = a_3 then i
         else a_2 q in
     let a_7 = a_6 a_3 in
     let a_8 = a_2 a_4 in
     let x_2 = cdiv i_1 (&2:int) in
     let x_3 = to_uint32 (i_1 - (&1:int)) in
     let x_4 = i_1 - i_2 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> a_7 = a_8
     ==> (&0:int) < i_1
     ==> (&0:int) <= i_2
     ==> i_2 < x_2
     ==> i_2 <= x_2
     ==> region (FST a) <= (&0:int)
     ==> i_2 + x_2 <= i_1
     ==> i_2 <= x_3
     ==> i_2 <= (&4294967294:int)
     ==> x_3 <= (&4294967295:int) + i_2
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 x_2
     ==> is_uint32 ((&1:int) + i_2)
     ==> valid_rw t a_1 i_1
     ==> valid_rw t a_4 (&1:int)
     ==> is_sint32 a_8
     ==> is_sint32 a_5
     ==> valid_rw t a_3 (&1:int)
     ==> is_sint32 a_7
     ==> p_unchanged a_2 t_2 a i_2 x_4
     ==> p_reverse_4 a_2 t_2 a (&0:int) i_2 x_4
     ==> p_reverse_4 a_2 t_2 a x_4 i_1 (&0:int)
     ==> p_reverse_4 a_6 t_2 a x_1 i_1 (&0:int)`;;
