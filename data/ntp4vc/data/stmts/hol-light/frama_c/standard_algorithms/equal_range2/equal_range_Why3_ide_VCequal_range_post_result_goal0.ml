(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_result_goal0:
  an equal-range verification condition asserting that the returned interval
  endpoints are ordered, nonnegative, and within the searched range, under
  the stated index bounds, ordering invariants, integer ranges, memory
  validity, linkage, and branch-state assumptions. This file contains no
  proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !s:int#int.
   !i_8 i_10:int.
   !a:int#int.
   !t_1:(int#int)->int.
   !i_7 i_11:int.
   !t:int->int.
   !i_1 i_2 i_3 i_4 i_5 i_6 i_9 i:int.
   !p_1 p_2 p_3 p:bool.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
     let shift_sint32 =
       \(q:int#int) (k:int). shift q k in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let valid_rd =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST q) /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let iss1_size_type_pair =
       \(q:int#int).
         is_uint32 (FST q) /\ is_uint32 (SND q) in
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
     let p_upperbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let x = FST s in
     let x_2 = i_8 - i_10 in
     let x_3 = cdiv x_2 (&2:int) in
     let x_4 = i_10 + x_3 in
     let x_5 = SND s in
     let a_1 = shift_sint32 a x_4 in
     let x_6 = t_1 a_1 in
     let x_7 =
       i_10 + to_uint32 (cdiv (to_uint32 x_2) (&2:int)) in
     let a_2 = shift_sint32 a i_10 in
     let a_3 = shift_sint32 a ((&1:int) + i_10 + x_3) in
     let x_9 = i_8 - (&1:int) - i_10 - x_3 in
     let x_10 = x - i_10 in
     let x_11 = x_5 - (&1:int) - i_10 - x_3 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> i_8 <= i_7
     ==> i_11 <= i_8
     ==> (&0:int) <= i_11
     ==> region (FST a) <= (&0:int)
     ==> iss1_size_type_pair s
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_uint32 i_5
     ==> is_uint32 i_6
     ==> is_uint32 i_7
     ==> is_uint32 i_8
     ==> is_uint32 i_9
     ==> is_uint32 i_10
     ==> is_uint32 i_11
     ==> is_sint32 i
     ==> p_sorted_1 t_1 a (&0:int) i_7
     ==> p_strictupperbound_1 t_1 a (&0:int) i_11 i
     ==> p_strictlowerbound_1 t_1 a i_8 i_7 i
     ==> valid_rd t (shift_sint32 a (&0:int)) i_7
     ==> (if i_11 < i_8
          then p_1 = F /\
               p_2 = F /\
               p_3 = F /\
               i_2 = i_1 /\
               i_5 = i_4 /\
               i_10 = i_9 /\
               i_11 = i_10 /\
               x = i_3 + i_10 /\
               x = i_6 + i_10 /\
               x_4 = i_4 /\
               x_4 = i_5 /\
               x_5 = (&1:int) + i_1 + i_10 + x_3 /\
               x_5 = (&1:int) + i_2 + i_10 + x_3 /\
               x_5 <= i_8 /\
               (&0:int) <= x /\
               i_10 <= x /\
               (&0:int) <= x_5 /\
               (&0:int) <= x_3 /\
               x_4 < i_8 /\
               x <= x_4 /\
               x_4 < x_5 /\
               x_6 <= i /\
               (&0:int) <= x_7 /\
               i <= x_6 /\
               x <= (&4294967295:int) /\
               x_5 <= (&4294967295:int) /\
               i_8 <= (&4294967295:int) + i_10 /\
               x_3 <= (&4294967295:int) /\
               x_4 <= (&4294967294:int) /\
               i_8 <= (&4294967296:int) + i_10 + x_3 /\
               x_7 <= (&4294967295:int) /\
               valid_rd t a_2 x_3 /\
               p_sorted_1 t_1 a_2 (&0:int) x_3 /\
               valid_rd t a_1 (&1:int) /\
               valid_rd t a_3 x_9 /\
               p_sorted_1 t_1 a_3 (&0:int) x_9 /\
               p_strictupperbound_1
                 t_1 a_2 (&0:int) x_10 x_6 /\
               p_strictlowerbound_1
                 t_1 a_3 x_11 x_9 x_6 /\
               p_lowerbound_1 t_1 a_2 x_10 x_3 x_6 /\
               p_upperbound_1 t_1 a_3 (&0:int) x_11 x_6
          else p = F /\ x = i_11 /\ x_5 = x)
     ==> x_5 <= i_7 /\ (&0:int) <= x /\ x <= x_5`;;
