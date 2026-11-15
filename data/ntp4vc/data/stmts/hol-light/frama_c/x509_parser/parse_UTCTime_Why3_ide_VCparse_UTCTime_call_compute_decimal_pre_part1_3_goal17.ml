(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_UTCTime_Why3_ide_VCparse_UTCTime_call_compute_decimal_pre_part1_3_goal17:
  an X.509 UTC-time parser verification condition concluding that the byte at
  offset six is at least the ASCII digit lower bound, under the stated address,
  integer-range, digit, linking, separation, and memory-validity assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_7:int#int.
   !t_1:(int#int)->int.
   !a_1 a a_2 a_3 a_4 a_5 a_6:int#int.
   !i i_1 i_3 i_2:int.
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
     let separated =
       \(p:int#int) (m:int) (q:int#int) (n:int).
         m <= (&0:int) \/
         n <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + n <= SND p \/
         SND p + m <= SND q in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let a_8 = shift a_7 (&0:int) in
     let a_9 = shift a_7 (&1:int) in
     let a_10 = shift a_7 (&14:int) in
     let a_11 = shift a_7 (&2:int) in
     let x = t_1 a_11 in
     let a_12 = shift a_7 (&3:int) in
     let x_1 = t_1 a_12 in
     let a_13 = shift a_7 (&4:int) in
     let x_2 = t_1 a_13 in
     let a_14 = shift a_7 (&5:int) in
     let x_3 = t_1 a_14 in
     let a_15 = shift a_7 (&6:int) in
     let x_4 = t_1 a_15 in
     let a_16 = shift a_7 (&7:int) in
     ~(a_1 = a)
     ==> ~(a_2 = a)
     ==> ~(a_2 = a_1)
     ==> ~(a_3 = a)
     ==> ~(a_3 = a_1)
     ==> ~(a_3 = a_2)
     ==> ~(a_4 = a)
     ==> ~(a_4 = a_1)
     ==> ~(a_4 = a_2)
     ==> ~(a_4 = a_3)
     ==> ~(a_5 = a)
     ==> ~(a_5 = a_1)
     ==> ~(a_5 = a_2)
     ==> ~(a_5 = a_3)
     ==> ~(a_5 = a_4)
     ==> ~(a_6 = a)
     ==> ~(a_6 = a_1)
     ==> ~(a_6 = a_2)
     ==> ~(a_6 = a_3)
     ==> ~(a_6 = a_4)
     ==> ~(a_6 = a_5)
     ==> ~(((&0:int),(&0:int)) = a_7)
     ==> t_1 a_8 = (&23:int)
     ==> t_1 a_9 = (&13:int)
     ==> t_1 a_10 = (&90:int)
     ==> (&0:int) <= i
     ==> (&0:int) <= i_1
     ==> (&0:int) <= i_3
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> region (FST a_4) <= (&0:int)
     ==> region (FST a_5) <= (&0:int)
     ==> region (FST a_6) <= (&0:int)
     ==> region (FST a_7) <= (&0:int)
     ==> --(&1900:int) <= i
     ==> (&12:int) <= i_2
     ==> (&15:int) <= i_1
     ==> (&50:int) <= i
     ==> i <= (&99:int)
     ==> i_3 <= (&99:int)
     ==> i <= (&63635:int)
     ==> i <= (&2147481747:int)
     ==> (&48:int) <= x
     ==> (&48:int) <= x_1
     ==> (&48:int) <= x_2
     ==> (&48:int) <= x_3
     ==> x <= (&57:int)
     ==> x_1 <= (&57:int)
     ==> x_2 <= (&57:int)
     ==> x_3 <= (&57:int)
     ==> linked t
     ==> is_uint8 i
     ==> is_uint8 i_2
     ==> is_uint8 i_3
     ==> is_uint16 i
     ==> is_uint16 i_1
     ==> valid_rw t a (&1:int)
     ==> valid_rw t a_1 (&1:int)
     ==> valid_rw t a_2 (&1:int)
     ==> valid_rw t a_3 (&1:int)
     ==> valid_rw t a_4 (&1:int)
     ==> valid_rw t a_5 (&1:int)
     ==> valid_rw t a_6 (&1:int)
     ==> is_uint8 x
     ==> is_uint8 x_1
     ==> is_uint8 x_2
     ==> is_uint8 x_3
     ==> is_uint8 x_4
     ==> is_uint8 (t_1 a_16)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_12 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> valid_rd t a_14 (&1:int)
     ==> valid_rd t a_15 (&1:int)
     ==> valid_rd t a_16 (&1:int)
     ==> valid_rd t a_10 (&1:int)
     ==> separated a (&1:int) a_8 i_1
     ==> separated a_1 (&1:int) a_8 i_1
     ==> separated a_2 (&1:int) a_8 i_1
     ==> separated a_3 (&1:int) a_8 i_1
     ==> separated a_4 (&1:int) a_8 i_1
     ==> separated a_5 (&1:int) a_8 i_1
     ==> separated a_6 (&1:int) a_8 i_1
     ==> valid_rd t (shift a_7 ((&2:int) + i_2)) (&1:int)
     ==> ((&0:int) < i_1
          ==> valid_rd t a_8 i_1)
     ==> (!i_4:int.
            let x_5 = t_1 (shift a_7 ((&2:int) + i_4)) in
            (&0:int) <= i_4
            ==> i_4 < i_2
            ==> (&48:int) <= x_5 /\ x_5 <= (&57:int))
     ==> (&48:int) <= x_4`;;
