(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14:
  an X.509 length-parser memory-access verification condition concluding that
  the byte two positions after the input address is readable, under the stated
  address-separation, region, byte-mask, integer-range, linking, and memory-
  validity assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a a_2:int#int.
   !t_1:(int#int)->int.
   !i:int.
   !t:int->int.
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
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let land_127 =
       \z:int. z rem (&128:int) in
     let bit_test_7 =
       \z:int.
         ~((z div (&128:int)) rem (&2:int) = (&0:int)) in
     let x = FST a_1 in
     let x_1 = FST a in
     let x_2 = FST a_2 in
     let a_3 = shift a_1 (&0:int) in
     let x_3 = t_1 a_3 in
     ~(i = (&0:int))
     ==> ~(a_2 = a)
     ==> ~(((&0:int),(&0:int)) = a_1)
     ==> ~(x = x_1)
     ==> ~(x_2 = x)
     ==> ~(x_3 = (&128:int))
     ==> land_127 x_3 = (&2:int)
     ==> (&0:int) <= i
     ==> region x_1 <= (&0:int)
     ==> region x <= (&0:int)
     ==> region x_2 <= (&0:int)
     ==> (&3:int) <= i
     ==> linked t
     ==> is_uint16 i
     ==> valid_rw t a (&1:int)
     ==> valid_rw t a_2 (&1:int)
     ==> is_uint8 x_3
     ==> bit_test_7 x_3
     ==> valid_rd t a_3 (&1:int)
     ==> ((&0:int) < i
          ==> valid_rd t a_3 i)
     ==> valid_rd t (shift a_1 (&2:int)) (&1:int)`;;
