(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3:
  a find-next-bit memory-access verification condition concluding that the
  shifted scan address is readable for one cell, under the stated index,
  integer-range, memory-validity, region, and linkage assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_size:int.
   !a:int#int.
   !i_2 i i_1:int.
   !t:int->int.
   !t_1:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let a_1 = shift a i_2 in
     ((&0:int) < l_size /\ l_size <= (&2147483647:int))
     ==> i_2 < i
     ==> i_1 <= i_2
     ==> i <= l_size
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint8 (t_1 a_1)
     ==> valid_rd t (shift a (&0:int)) i
     ==> (!i_3:int.
            i_1 <= i_3
            ==> i_3 < i_2
            ==> t_1 (shift a i_3) = (&0:int))
     ==> valid_rd t a_1 (&1:int)`;;
