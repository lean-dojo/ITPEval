(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/StrictUpperBoundShift_Why3_ide_VCStrictUpperBoundShift_post_goal0:
  a selection-sort verification condition stating that a strict upper bound
  on a shifted array segment induces the same strict upper bound on the
  corresponding segment of the original array, under the stated integer
  bounds. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !i_2 i_1:int.
   !a:int#int.
   !i:int.
   !t:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_strictupperbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) < value in
     i_2 <= i_1
     ==> region (FST a) <= (&0:int)
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_sint32 i
     ==> p_strictupperbound_1
           t (shift a i_2) (&0:int) (i_1 - i_2) i
     ==> p_strictupperbound_1 t a i_2 i_1 i`;;
