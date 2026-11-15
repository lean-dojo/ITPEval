(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_7_part04_goal20:
  an X.509 UTF-8 string-checker memory-access verification condition concluding
  that the byte one position after the current address is readable, under the
  stated address, region, integer-range, byte-value, and memory-validity
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a:int#int.
   !i i_1:int.
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
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let a_2 = shift a_1 (&0:int) in
     let x = t_1 a_2 in
     ~(i = (&0:int))
     ==> ~(i_1 = (&0:int))
     ==> ~(((&0:int),(&0:int)) = a)
     ==> ~(x = (&240:int))
     ==> ~(x = (&244:int))
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> (&4:int) <= i
     ==> (&128:int) <= x
     ==> (&194:int) <= x
     ==> (&224:int) <= x
     ==> (&240:int) <= x
     ==> x <= (&244:int)
     ==> linked t
     ==> is_uint16 i
     ==> is_uint16 i_1
     ==> is_uint8 x
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_2 i
     ==> ((&0:int) < i_1
          ==> valid_rd t (shift a (&0:int)) i_1)
     ==> valid_rd t (shift a_1 (&1:int)) (&1:int)`;;
