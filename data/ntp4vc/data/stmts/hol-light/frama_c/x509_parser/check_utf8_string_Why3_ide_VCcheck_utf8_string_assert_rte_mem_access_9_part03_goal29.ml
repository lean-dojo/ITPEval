(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29:
  an X.509 UTF-8 string-checker memory-access verification condition concluding
  that the fourth byte is readable after a four-byte leading character and
  two continuation-byte checks, under the stated address, region, integer-
  range, byte-mask, linking, and memory-validity assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1:int#int.
   !t_1:(int#int)->int.
   !i i_1:int.
   !a:int#int.
   !t:int->int.
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
     let land_192 =
       \z:int.
         (&64:int) * ((z div (&64:int)) rem (&4:int)) in
     let a_2 = shift a_1 (&0:int) in
     let a_3 = shift a_1 (&1:int) in
     let x = t_1 a_3 in
     let a_4 = shift a_1 (&2:int) in
     let x_1 = t_1 a_4 in
     let a_5 = shift a_1 (&3:int) in
     ~(i = (&0:int))
     ==> ~(i_1 = (&0:int))
     ==> ~(((&0:int),(&0:int)) = a)
     ==> t_1 a_2 = (&244:int)
     ==> land_192 x = (&128:int)
     ==> land_192 x_1 = (&128:int)
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> (&4:int) <= i
     ==> (&128:int) <= x
     ==> x <= (&143:int)
     ==> linked t
     ==> is_uint16 i
     ==> is_uint16 i_1
     ==> is_uint8 x
     ==> is_uint8 x_1
     ==> is_uint8 (t_1 a_5)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_2 i
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> ((&0:int) < i_1
          ==> valid_rd t (shift a (&0:int)) i_1)
     ==> valid_rd t a_5 (&1:int)`;;
