(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_decimal_pre_part1_5_goal32:
  an X.509 GeneralizedTime parser verification condition asserting that the
  character at offset fourteen is at least the ASCII digit zero, under the
  stated address, integer-bound, digit-range, linking, memory-validity, and
  separation assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_7:int#int.
   !t_1:(int#int)->int.
   !a_1 a a_2 a_3 a_4 a_5 a_6:int#int.
   !i i_2 i_3 i_4 i_5 i_6 i_1:int.
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
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let a_8 = shift a_7 (&0:int) in
     let a_9 = shift a_7 (&1:int) in
     let a_10 = shift a_7 (&16:int) in
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
     let x_5 = t_1 a_16 in
     let a_17 = shift a_7 (&8:int) in
     let x_6 = t_1 a_17 in
     let a_18 = shift a_7 (&9:int) in
     let x_7 = t_1 a_18 in
     let a_19 = shift a_7 (&10:int) in
     let x_8 = t_1 a_19 in
     let a_20 = shift a_7 (&11:int) in
     let x_9 = t_1 a_20 in
     let a_21 = shift a_7 (&12:int) in
     let x_10 = t_1 a_21 in
     let a_22 = shift a_7 (&13:int) in
     let x_11 = t_1 a_22 in
     let a_23 = shift a_7 (&14:int) in
     let x_12 = t_1 a_23 in
     let a_24 = shift a_7 (&15:int) in
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
     ==> t_1 a_8 = (&24:int)
     ==> t_1 a_9 = (&15:int)
     ==> t_1 a_10 = (&90:int)
     ==> (&0:int) <= i
     ==> (&0:int) <= i_2
     ==> (&0:int) <= i_3
     ==> (&0:int) <= i_4
     ==> (&0:int) <= i_5
     ==> (&0:int) <= i_6
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> region (FST a_4) <= (&0:int)
     ==> region (FST a_5) <= (&0:int)
     ==> region (FST a_6) <= (&0:int)
     ==> region (FST a_7) <= (&0:int)
     ==> (&14:int) <= i_1
     ==> (&17:int) <= i
     ==> i_3 <= (&99:int)
     ==> i_4 <= (&99:int)
     ==> i_5 <= (&99:int)
     ==> i_6 <= (&99:int)
     ==> i_2 <= (&9999:int)
     ==> (&48:int) <= x
     ==> (&48:int) <= x_1
     ==> (&48:int) <= x_2
     ==> (&48:int) <= x_3
     ==> (&48:int) <= x_4
     ==> (&48:int) <= x_5
     ==> (&48:int) <= x_6
     ==> (&48:int) <= x_7
     ==> (&48:int) <= x_8
     ==> (&48:int) <= x_9
     ==> (&48:int) <= x_10
     ==> (&48:int) <= x_11
     ==> x <= (&57:int)
     ==> x_1 <= (&57:int)
     ==> x_2 <= (&57:int)
     ==> x_3 <= (&57:int)
     ==> x_4 <= (&57:int)
     ==> x_5 <= (&57:int)
     ==> x_6 <= (&57:int)
     ==> x_7 <= (&57:int)
     ==> x_8 <= (&57:int)
     ==> x_9 <= (&57:int)
     ==> x_10 <= (&57:int)
     ==> x_11 <= (&57:int)
     ==> linked t
     ==> is_uint8 i_1
     ==> is_uint8 i_3
     ==> is_uint8 i_4
     ==> is_uint8 i_5
     ==> is_uint8 i_6
     ==> is_uint16 i
     ==> is_uint16 i_2
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
     ==> is_uint8 x_5
     ==> is_uint8 x_6
     ==> is_uint8 x_7
     ==> is_uint8 x_8
     ==> is_uint8 x_9
     ==> is_uint8 x_10
     ==> is_uint8 x_11
     ==> is_uint8 x_12
     ==> is_uint8 (t_1 a_24)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_12 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> valid_rd t a_14 (&1:int)
     ==> valid_rd t a_15 (&1:int)
     ==> valid_rd t a_16 (&1:int)
     ==> valid_rd t a_17 (&1:int)
     ==> valid_rd t a_18 (&1:int)
     ==> valid_rd t a_19 (&1:int)
     ==> valid_rd t a_20 (&1:int)
     ==> valid_rd t a_21 (&1:int)
     ==> valid_rd t a_22 (&1:int)
     ==> valid_rd t a_23 (&1:int)
     ==> valid_rd t a_24 (&1:int)
     ==> valid_rd t a_10 (&1:int)
     ==> separated a (&1:int) a_8 i
     ==> separated a_1 (&1:int) a_8 i
     ==> separated a_2 (&1:int) a_8 i
     ==> separated a_3 (&1:int) a_8 i
     ==> separated a_4 (&1:int) a_8 i
     ==> separated a_5 (&1:int) a_8 i
     ==> separated a_6 (&1:int) a_8 i
     ==> valid_rd t (shift a_7 ((&2:int) + i_1)) (&1:int)
     ==> ((&0:int) < i ==> valid_rd t a_8 i)
     ==> (!i_7:int.
            let x_13 = t_1 (shift a_7 ((&2:int) + i_7)) in
            (&0:int) <= i_7
            ==> i_7 < i_1
            ==> (&48:int) <= x_13 /\ x_13 <= (&57:int))
     ==> (&48:int) <= x_12`;;
