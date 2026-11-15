(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal6:
  preservation of a strlen loop invariant, concluding the endpoint-offset
  equality after advancing the current address by one byte, under the stated
  memory, string-length, address-order, signed-byte, and offset assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let is_uint64 =
       \z:int.
         (&0:int) <= z /\ z < (&18446744073709551616:int) in
     let p_valid_str =
       \(malloc:int->int)
        (mchar:(int#int)->int)
        (s:int#int).
         ?n:int.
           mchar (shift s n) = (&0:int) /\
           is_uint64 n /\
           valid_rw malloc (shift s (&0:int)) ((&1:int) + n) /\
           (!j:int.
              j <= n
              ==> is_sint8 (mchar (shift s j))) in
     let x = t_1 a in
     let x_1 = l_strlen t_1 a_1 in
     let x_2 = SND a_1 + x_1 in
     let x_3 = SND a in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!z:int. to_uint64 (to_uint64 z) = to_uint64 z)
     ==> (!mchar s.
            (if mchar (shift s (&0:int)) = (&0:int)
             then l_strlen mchar s = (&0:int)
             else
               to_uint64
                 ((&1:int) + l_strlen mchar (shift s (&1:int))) =
               l_strlen mchar s))
     ==> (!mchar s. is_uint64 (l_strlen mchar s))
     ==> ~(x = (&0:int))
     ==> x_2 = x_3 + l_strlen t_1 a
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> addr_le a_1 a
     ==> is_sint8 x
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> addr_le a (shift a_1 x_1)
     ==> (&1:int) + x_3 + l_strlen t_1 (shift a (&1:int)) = x_2`;;
