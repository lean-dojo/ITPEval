(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_upper_bound_pre_sorted_goal28:
  an equal-range verification condition asserting that the suffix subrange
  passed to upper_bound is sorted, under the stated index bounds, ordering
  invariants, integer ranges, memory validity, and linkage assumptions. This
  file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !i_1 i_4 i_3:int.
   !a:int#int.
   !t_1:(int#int)->int.
   !i_2 i:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let shift_sint32 =
       \(p:int#int) (k:int). shift p k in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_sorted_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     let p_lowerbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value <= mint (shift base_addr j) in
     let p_strictlowerbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value < mint (shift base_addr j) in
     let p_strictupperbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) < value in
     let x = i_1 + i_4 in
     let x_2 = i_3 - i_4 in
     let x_3 = cdiv x_2 (&2:int) in
     let x_4 = i_4 + x_3 in
     let a_1 = shift_sint32 a x_4 in
     let x_5 = t_1 a_1 in
     let x_6 =
       i_4 + to_uint32 (cdiv (to_uint32 x_2) (&2:int)) in
     let a_2 = shift_sint32 a i_4 in
     let x_7 = (&1:int) + i_4 + x_3 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (&0:int) <= i_1
     ==> i_3 <= i_2
     ==> i_4 <= i_3
     ==> (&0:int) <= i_4
     ==> i_4 < i_3
     ==> (&0:int) <= x
     ==> region (FST a) <= (&0:int)
     ==> (&0:int) <= x_3
     ==> i_1 <= x_3
     ==> x_4 < i_3
     ==> x_5 <= i
     ==> (&0:int) <= x_6
     ==> i <= x_5
     ==> x <= (&4294967295:int)
     ==> i_3 <= (&4294967295:int) + i_4
     ==> x_3 <= (&4294967295:int)
     ==> x_4 <= (&4294967294:int)
     ==> i_3 <= (&4294967296:int) + i_4 + x_3
     ==> x_6 <= (&4294967295:int)
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_sint32 i
     ==> p_sorted_1 t_1 a (&0:int) i_2
     ==> p_strictupperbound_1 t_1 a (&0:int) i_4 i
     ==> p_strictlowerbound_1 t_1 a i_3 i_2 i
     ==> valid_rd t (shift_sint32 a (&0:int)) i_2
     ==> valid_rd t a_2 x_3
     ==> p_sorted_1 t_1 a_2 (&0:int) x_3
     ==> is_uint32 x_4
     ==> is_uint32 x_7
     ==> is_sint32 x_5
     ==> valid_rd t a_1 (&1:int)
     ==> p_strictupperbound_1 t_1 a_2 (&0:int) i_1 x_5
     ==> p_lowerbound_1 t_1 a_2 i_1 x_3 x_5
     ==> p_sorted_1 t_1 (shift_sint32 a x_7) (&0:int)
           (i_3 - (&1:int) - i_4 - x_3)`;;
