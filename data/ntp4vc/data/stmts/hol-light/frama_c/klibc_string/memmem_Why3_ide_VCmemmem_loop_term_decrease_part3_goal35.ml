(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_loop_term_decrease_part3_goal35:
  a memmem loop-variant decrease verification condition asserting that the
  current nonnegative search offset is strictly below its incremented
  unsigned-32-bit conversion, under the stated memory, separation, byte-range,
  index-bound, and mismatch assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !a_8 a_9:int#int.
   !t_1:(int#int)->int.
   !a_1 a:int#int.
   !i_2:int.
   !a_6:int#int.
   !i_1:int.
   !a_7:int#int.
   !i:int.
   !t:int->int.
   !a_5 a_4 a_3 a_2:int#int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let x = FST a_8 in
     let x_1 = FST a_9 in
     let x_2 = t_1 (shift a_1 (&0:int)) in
     let x_3 = t_1 (shift a i_2) in
     let x_4 = t_1 (shift a_1 (&1:int)) in
     let x_5 = to_uint32 ((&1:int) + i_2) in
     let x_6 = t_1 (shift a x_5) in
     let a_10 = shift a_8 (&0:int) in
     let a_11 = shift a_9 (&0:int) in
     let a_12 = shift a_6 (&0:int) in
     let x_7 = to_uint32 (i_1 - (&2:int)) in
     let a_13 = shift a_7 (&0:int) in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(i = (&0:int))
     ==> ~(i_1 = (&0:int))
     ==> ~(i_1 = (&1:int))
     ==> x = FST a_1
     ==> x_1 = FST a
     ==> ~(x_2 = x_3)
     ==> x_4 = x_2
     ==> x_6 = x_4
     ==> (&0:int) <= i
     ==> i_1 <= i
     ==> (&0:int) <= i_1
     ==> (&0:int) <= i_2
     ==> region x <= (&0:int)
     ==> region x_1 <= (&0:int)
     ==> i_2 <= to_uint32 (i - i_1)
     ==> i_1 + i_2 <= (&2:int) + i
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint8 x_3
     ==> is_uint8 x_2
     ==> is_uint8 x_4
     ==> valid_rw t a_10 i_1
     ==> valid_rw t a_11 i
     ==> separated a_11 i a_10 i_1
     ==> valid_rw t a_12 x_7
     ==> valid_rw t a_13 x_7
     ==> separated a_13 x_7 a_12 x_7
     ==> is_uint8 x_6
     ==> ((&0:int) < x_7
          ==> ~(?i_3:int.
                 ~(t_1 (shift a_5 i_3) = t_1 (shift a_4 i_3)) /\
                 (&0:int) <= i_3 /\
                 i_3 < x_7))
     ==> (!i_3:int.
           (&0:int) <= i_3
           ==> i_3 < i_2
           ==> (?i_4:int.
                (&0:int) <= i_4
                ==> (&3:int) + i_4 <= i_1
                ==> ~(t_1 (shift a_3 ((&2:int) + i_4 + i_3)) =
                      t_1 (shift a_2 ((&2:int) + i_4)))))
     ==> i_2 < x_5`;;
