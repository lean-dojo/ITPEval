(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/SortedShift_Why3_ide_VCSortedShift_post_goal0:
  a selection-sort verification condition stating that sortedness of an
  integer-indexed array segment is preserved when its base address is shifted
  to the start of that segment. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !i_1 i:int.
   !a:int#int.
   !t:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let p_sorted_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     i_1 <= i
     ==> region (FST a) <= (&0:int)
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> p_sorted_1 t a i_1 i
     ==> p_sorted_1 t (shift a i_1) (&0:int) (i - i_1)`;;
