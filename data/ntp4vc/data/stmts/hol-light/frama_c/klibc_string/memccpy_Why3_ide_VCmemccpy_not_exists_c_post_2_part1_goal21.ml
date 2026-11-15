(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_not_exists_c_post_2_part1_goal21:
  a memccpy postcondition verification condition asserting equality of the
  updated source and destination memory values at index i_2, under the stated
  bounds, memory-validity, separation, address-order, linking, constancy,
  prefix-equality, and byte-exclusion assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_sint8:int->int.
   !a_1:int#int.
   !i_1 i:int.
   !t_1 t_2:(int#int)->int.
   !a:int#int.
   !i_3 i_2:int.
   !t:int->int.
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
     let a_2 = shift a_1 (&0:int) in
     let x = i_1 - i in
     let a_3 = havoc t_1 t_2 a_2 x in
     let a_4 = shift a x in
     let a_5 = a_3 a_4 in
     let a_6 = shift a (&0:int) in
     let a_7 = shift a_1 x in
     let a_8 = update a_3 a_7 a_5 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> ~(i = (&0:int))
     ==> a_5 = to_sint8 i_3
     ==> (&0:int) < i_1
     ==> (&0:int) <= i
     ==> i <= i_1
     ==> (&0:int) <= i_2
     ==> i_2 < i_1
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> --(&128:int) <= i_3
     ==> i_3 <= (&127:int)
     ==> linked t
     ==> sconst t_2
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_sint32 i_3
     ==> valid_rw t a_6 i_1
     ==> valid_rw t a_2 i_1
     ==> separated a_6 i_1 a_2 i_1
     ==> addr_le a a_4
     ==> addr_le a_1 a_7
     ==> addr_le a_4 (shift a i_1)
     ==> addr_le a_7 (shift a_1 i_1)
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> a_3 (shift a_1 i_4) = a_3 (shift a i_4))
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 < i_1
           ==> ~(a_5 = t_2 (shift a i_4)))
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> ~(a_5 = a_3 (shift a_1 i_4)))
     ==> a_8 (shift a_1 i_2) = a_8 (shift a i_2)`;;
