(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/is_sorted/is_sorted_Why3_ide_VCis_sorted_post_goal0:
  an array-sortedness verification condition stating that the array segment
  is sorted exactly when the computed integer flag is nonzero, under the
  stated integer-range, memory-validity, linkage, and branch-state
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !i_2:int.
   !a:int#int.
   !t:int->int.
   !i:int.
   !i_1:int.
   !p:bool.
   !t_1:(int#int)->int.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
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
     let p_weaklysorted_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> (&2:int) + j <= upper
           ==> mint (shift base_addr j) <=
               mint (shift base_addr ((&1:int) + j)) in
     let p_sorted_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     let x = (&1:int) + i_2 in
     let a_1 = shift a i_2 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_2
     ==> is_sint32 i_1
     ==> valid_rd t (shift a (&0:int)) i
     ==> (if (&0:int) < i
          then p = F /\
               p_weaklysorted_1 t_1 a (&0:int) x /\
               (if (&2:int) + i_2 <= i
                then i_1 = (&0:int) /\
                     t_1 (shift a x) < t_1 a_1 /\
                     i_2 <= (&4294967294:int) /\
                     valid_rd t a_1 (&1:int) /\
                     valid_rd t
                       (shift a (to_uint32 x)) (&1:int)
                else i_1 = (&1:int))
          else i_1 = (&1:int))
     ==> (p_sorted_1 t_1 a (&0:int) i <=>
          ~(i_1 = (&0:int)))`;;
