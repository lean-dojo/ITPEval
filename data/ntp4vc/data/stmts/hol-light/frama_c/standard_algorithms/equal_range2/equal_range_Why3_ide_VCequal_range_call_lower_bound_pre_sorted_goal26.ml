(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26:
  an equal-range verification condition asserting that the midpoint-length
  subrange passed to lower_bound is sorted, under the stated index bounds,
  ordering invariants, integer ranges, memory validity, and linkage
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !i_2 i_3:int.
   !a:int#int.
   !t_1:(int#int)->int.
   !i_1 i:int.
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
     let x = i_2 - i_3 in
     let x_1 = cdiv x (&2:int) in
     let x_2 = i_3 + x_1 in
     let a_1 = shift_sint32 a x_2 in
     let x_3 = t_1 a_1 in
     let x_4 =
       i_3 + to_uint32 (cdiv (to_uint32 x) (&2:int)) in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> i_2 <= i_1
     ==> i_3 <= i_2
     ==> (&0:int) <= i_3
     ==> i_3 < i_2
     ==> region (FST a) <= (&0:int)
     ==> (&0:int) <= x_1
     ==> x_3 <= i
     ==> (&0:int) <= x_4
     ==> i <= x_3
     ==> i_2 <= (&4294967295:int) + i_3
     ==> x_1 <= (&4294967295:int)
     ==> x_4 <= (&4294967295:int)
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_sint32 i
     ==> p_sorted_1 t_1 a (&0:int) i_1
     ==> p_strictupperbound_1 t_1 a (&0:int) i_3 i
     ==> p_strictlowerbound_1 t_1 a i_2 i_1 i
     ==> valid_rd t (shift_sint32 a (&0:int)) i_1
     ==> is_uint32 x_2
     ==> is_sint32 x_3
     ==> valid_rd t a_1 (&1:int)
     ==> p_sorted_1 t_1 (shift_sint32 a i_3) (&0:int) x_1`;;
