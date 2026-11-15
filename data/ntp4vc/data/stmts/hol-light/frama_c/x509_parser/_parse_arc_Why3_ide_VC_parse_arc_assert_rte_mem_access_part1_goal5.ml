(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5:
  an X.509 arc-parser memory-access verification condition concluding that the
  byte at the current nonnegative offset is readable, under the stated address,
  region, shift, integer-range, bit-prefix, and memory-validity assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a a_2:int#int.
   !i_1 i i_2:int.
   !t:int->int.
   !t_1:(int#int)->int.
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
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let to_uint32 =
       \z:int. z rem (&4294967296:int) in
     let lsl =
       \(z:int) (k:int).
         z * ((&2:int) pow (num_of_int k)) in
     let bit_test =
       \(z:int) (k:int).
         ~((z div ((&2:int) pow (num_of_int k)))
           rem (&2:int) = (&0:int)) in
     ~(i_1 = (&0:int))
     ==> ~(a_2 = a)
     ==> ~(((&0:int),(&0:int)) = a_1)
     ==> ~(FST a_1 = FST a)
     ==> ~(FST a_2 = FST a_1)
     ==> (&0:int) <= i
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> i_2 <
         lsl (&1:int) (to_uint32 ((&7:int) * i))
     ==> i <= (&3:int)
     ==> i <= (&4:int)
     ==> (&5:int) <= i_1
     ==> lsl i_2 (&7:int) <= (&4294967295:int)
     ==> linked t
     ==> is_uint16 i
     ==> is_uint16 i_1
     ==> is_uint32 i_2
     ==> valid_rw t a (&1:int)
     ==> valid_rw t a_2 (&1:int)
     ==> ((&0:int) < i_1
          ==> valid_rd t (shift a_1 (&0:int)) i_1)
     ==> (!i_3:int.
            (&0:int) <= i_3
            ==> i_3 < i
            ==> bit_test (t_1 (shift a_1 i_3)) (&7:int))
     ==> valid_rd t (shift a_1 i) (&1:int)`;;
