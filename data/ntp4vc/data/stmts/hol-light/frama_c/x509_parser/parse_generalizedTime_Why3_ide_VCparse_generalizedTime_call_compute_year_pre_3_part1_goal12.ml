(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_year_pre_3_part1_goal12:
  an X.509 GeneralizedTime parser verification condition concluding that the
  character at offset four is at least the ASCII digit zero, under the stated
  address, integer-bound, digit-range, linking, memory-validity, and separation
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_7:int#int.
   !t_1:(int#int)->int.
   !a_1 a a_2 a_3 a_4 a_5 a_6:int#int.
   !i i_1:int.
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
     let a_12 = shift a_7 (&3:int) in
     let a_13 = shift a_7 (&4:int) in
     let x = t_1 a_13 in
     let a_14 = shift a_7 (&5:int) in
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
     ==> linked t
     ==> is_uint8 i_1
     ==> is_uint16 i
     ==> valid_rw t a (&1:int)
     ==> valid_rw t a_1 (&1:int)
     ==> valid_rw t a_2 (&1:int)
     ==> valid_rw t a_3 (&1:int)
     ==> valid_rw t a_4 (&1:int)
     ==> valid_rw t a_5 (&1:int)
     ==> valid_rw t a_6 (&1:int)
     ==> is_uint8 (t_1 a_11)
     ==> is_uint8 (t_1 a_12)
     ==> is_uint8 x
     ==> is_uint8 (t_1 a_14)
     ==> valid_rd t a_8 (&1:int)
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_11 (&1:int)
     ==> valid_rd t a_12 (&1:int)
     ==> valid_rd t a_13 (&1:int)
     ==> valid_rd t a_14 (&1:int)
     ==> valid_rd t a_10 (&1:int)
     ==> separated a (&1:int) a_8 i
     ==> separated a_1 (&1:int) a_8 i
     ==> separated a_2 (&1:int) a_8 i
     ==> separated a_3 (&1:int) a_8 i
     ==> separated a_4 (&1:int) a_8 i
     ==> separated a_5 (&1:int) a_8 i
     ==> separated a_6 (&1:int) a_8 i
     ==> valid_rd t (shift a_7 ((&2:int) + i_1)) (&1:int)
     ==> ((&0:int) < i
          ==> valid_rd t a_8 i)
     ==> (!i_2:int.
            let x_1 = t_1 (shift a_7 ((&2:int) + i_2)) in
            (&0:int) <= i_2
            ==> i_2 < i_1
            ==> (&48:int) <= x_1 /\ x_1 <= (&57:int))
     ==> (&48:int) <= x`;;
