(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6:
  a memchr loop-invariant preservation verification condition asserting that
  the byte at offset i_2 differs from the searched signed-byte value, under
  the stated index bounds, memory-validity, address-order, linking, constancy,
  integer-range, and prior byte-exclusion assumptions. This file contains no
  proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_sint8:int->int.
   !to_uint32:int->int.
   !a:int#int.
   !i_1 i:int.
   !t_1:(int#int)->int.
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
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let a_1 = shift a (i_1 - i) in
     let x = t_1 a_1 in
     let x_1 = to_sint8 i_3 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(i = (&0:int))
     ==> ~(x = x_1)
     ==> (&0:int) < i_1
     ==> (&0:int) <= i
     ==> i <= i_1
     ==> (&0:int) <= i_2
     ==> region (FST a) <= (&0:int)
     ==> i_2 + to_uint32 (i - (&1:int)) < i_1
     ==> --(&128:int) <= i_3
     ==> i_3 <= (&127:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_sint32 i_3
     ==> valid_rw t (shift a (&0:int)) i_1
     ==> addr_le a a_1
     ==> addr_le a_1 (shift a i_1)
     ==> is_sint8 x
     ==> (!i_4:int.
           (&0:int) <= i_4
           ==> i_4 + i < i_1
           ==> ~(t_1 (shift a i_4) = x_1))
     ==> ~(t_1 (shift a i_2) = x_1)`;;
