(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_exists_c_post_part1_goal16:
  a memccpy postcondition verification condition stating that a one-cell
  destination-memory update preserves the specified source/destination prefix
  equality and byte-exclusion invariants, under the given bounds, memory
  validity, separation, and address-order assumptions. This file contains no
  proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_sint8:int->int.
   !t_2:(int#int)->int.
   !a:int#int.
   !i_2:int.
   !a_1:int#int.
   !i_1 i:int.
   !t_1:(int#int)->int.
   !i_3:int.
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
     let x = t_2 (shift a i_2) in
     let a_2 = shift a_1 (&0:int) in
     let x_1 = i_1 - i in
     let a_3 = havoc t_1 t_2 a_2 x_1 in
     let a_4 = shift a x_1 in
     let a_5 = shift a (&0:int) in
     let a_6 = shift a_1 x_1 in
     let a_7 = update a_3 a_6 x in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> ~(i = (&0:int))
     ==> x = to_sint8 i_3
     ==> a_3 a_4 = x
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
     ==> valid_rw t a_5 i_1
     ==> valid_rw t a_2 i_1
     ==> separated a_5 i_1 a_2 i_1
     ==> addr_le a a_4
     ==> addr_le a_1 a_6
     ==> addr_le a_4 (shift a i_1)
     ==> addr_le a_6 (shift a_1 i_1)
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> a_3 (shift a_1 i_4) = a_3 (shift a i_4))
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> ~(a_3 (shift a_1 i_4) = x))
     ==> a_7 a_4 = x /\
         (&0:int) < i /\
         (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i <= i_1
           ==> a_7 (shift a_1 i_4) = a_7 (shift a i_4)) /\
         (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> ~(a_7 (shift a i_4) = x))`;;
