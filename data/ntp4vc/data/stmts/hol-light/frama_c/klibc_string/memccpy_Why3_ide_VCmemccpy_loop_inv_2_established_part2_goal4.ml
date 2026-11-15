(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_2_established_part2_goal4:
  a memccpy loop-invariant establishment verification condition asserting
  address order after a positive shift, under the stated integer-range,
  memory-validity, separation, linking, and constancy assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !a a_1:int#int.
   !i i_1:int.
   !t:int->int.
   !t_1:(int#int)->int.
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
     let a_2 = shift a (&0:int) in
     let a_3 = shift a_1 (&0:int) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (&0:int) < i
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> --(&128:int) <= i_1
     ==> i_1 <= (&127:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> valid_rw t a_2 i
     ==> valid_rw t a_3 i
     ==> separated a_2 i a_3 i
     ==> addr_le a_1 (shift a_1 i)`;;
