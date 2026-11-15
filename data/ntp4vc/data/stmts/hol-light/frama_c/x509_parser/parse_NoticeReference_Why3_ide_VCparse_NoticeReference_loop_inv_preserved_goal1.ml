(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/x509_parser/parse_NoticeReference_Why3_ide_VCparse_NoticeReference_loop_inv_preserved_goal1:
  preservation of an X.509 NoticeReference parser loop invariant, concluding
  readability of the remaining portion of an address range under the stated
  integer bounds, address, region, linking, and memory-validity assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a:int#int.
   !i_4 i_5 i i_1 i_2 i_3:int.
   !a_2:int#int.
   !i_6:int.
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
     let x = FST a_1 in
     let x_1 = FST a in
     let a_3 = shift a_1 i_4 in
     let a_4 = shift a_1 (i_4 + i_5 - i) in
     let x_3 = i_4 + i_5 in
     let x_4 = i_1 - i_2 in
     ~(i = (&0:int))
     ==> ~(i_1 = (&0:int))
     ==> ~(i_3 = (&0:int))
     ==> ~(i_5 = (&0:int))
     ==> ~(((&0:int),(&0:int)) = a_1)
     ==> ~(((&0:int),(&0:int)) = a_2)
     ==> ~(x = x_1)
     ==> ~(a_3 = ((&0:int),(&0:int)))
     ==> ~(a_4 = ((&0:int),(&0:int)))
     ==> (&0:int) <= i
     ==> i_6 <= i
     ==> (&0:int) <= i_1
     ==> i_2 <= i_1
     ==> (&0:int) <= i_3
     ==> i_4 <= i_3
     ==> i_5 <= i_3
     ==> (&0:int) <= i_5
     ==> (&0:int) <= i_6
     ==> x_3 <= i_3
     ==> (&0:int) <= x_3
     ==> region x_1 <= (&0:int)
     ==> region x <= (&0:int)
     ==> --(&2147483648:int) <= i
     ==> --(&2147483648:int) <= i_6
     ==> (&2:int) <= i_4
     ==> (&3:int) <= i_2
     ==> i <= (&65535:int)
     ==> i_6 <= (&65535:int)
     ==> i <= (&2147483647:int)
     ==> i_6 <= (&2147483647:int)
     ==> --(&2147483648:int) <= x_3
     ==> x_3 <= (&65535:int)
     ==> x_3 <= (&2147483647:int)
     ==> (&2:int) + i_6 <= i
     ==> i_1 <= (&65535:int) + i_2
     ==> i_1 <= (&2147483647:int) + i_2
     ==> i_2 <= (&2147483648:int) + i_1
     ==> linked t
     ==> is_uint16 i
     ==> is_uint16 i_1
     ==> is_uint16 i_2
     ==> is_uint16 i_3
     ==> is_uint16 i_4
     ==> is_uint16 i_5
     ==> is_uint16 i_6
     ==> valid_rw t a (&1:int)
     ==> is_uint16 (i - i_6)
     ==> is_uint16 x_4
     ==> is_uint16 (i_5 - i)
     ==> valid_rd t (shift a_2 (&0:int)) i_1
     ==> ((&0:int) < i_3
          ==> valid_rd t (shift a_1 (&0:int)) i_3)
     ==> ((&0:int) < i_5
          ==> valid_rd t a_3 i_5)
     ==> ((&0:int) < i
          ==> valid_rd t a_4 i)
     ==> valid_rd t (shift a_2 i_2) x_4`;;
