(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/binary_search/binary_search_Why3_ide_VCbinary_search_post_result_goal0:
  a binary-search postcondition verification condition stating that the
  returned integer is nonzero exactly when the searched value occurs at an
  index in the searched range, under the stated bounds, sortedness, memory,
  linkage, and branch-result assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a:int#int.
   !i_2:int.
   !t_1:(int#int)->int.
   !i_1:int.
   !t:int->int.
   !i:int.
   !i_3:int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
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
     let p_strictupperbound_1 =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) < value in
     let a_1 = shift a i_2 in
     let x = t_1 a_1 in
     i_2 <= i_1
     ==> (&0:int) <= i_2
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_sint32 i
     ==> is_sint32 i_3
     ==> p_sorted_1 t_1 a (&0:int) i_1
     ==> is_sint32 x
     ==> p_lowerbound_1 t_1 a i_2 i_1 i
     ==> p_strictupperbound_1 t_1 a (&0:int) i_2 i
     ==> valid_rd t (shift a (&0:int)) i_1
     ==> (if i_2 < i_1
          then valid_rd t a_1 (&1:int) /\
               (if x <= i
                then i_3 = (&1:int)
                else i_3 = (&0:int))
          else i_3 = (&0:int))
     ==> ((?i_4:int.
             t_1 (shift a i_4) = i /\
             (&0:int) <= i_4 /\
             i_4 < i_1) <=>
          ~(i_3 = (&0:int)))`;;
