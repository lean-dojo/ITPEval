(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strcat_Why3_ide_VCstrcat_loop_inv_2_preserved_goal3:
  preservation of a string-concatenation loop invariant, concluding that the
  one-byte successor of the current address is a valid string under
  the stated memory, address-order, range, and non-null-character assumptions.
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
   !a_2 a a_1:int#int.
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
     let x = t_1 a_2 in
     let x_1 = l_strlen t_1 a in
     let a_3 = shift a x_1 in
     let x_2 = l_strlen t_1 a_1 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!mchar s.
            (if mchar (shift s (&0:int)) = (&0:int)
             then l_strlen mchar s = (&0:int)
             else
               to_uint64
                 ((&1:int) + l_strlen mchar (shift s (&1:int))) =
               l_strlen mchar s))
     ==> (!mchar s. is_uint64 (l_strlen mchar s))
     ==> ~(x = (&0:int))
     ==> t_1 a_3 = (&0:int)
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> x_1 + x_2 <= (&18446744073709551615:int)
     ==> linked t
     ==> sconst t_1
     ==> addr_le a a_2
     ==> is_sint8 x
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> p_valid_str t t_1 a_2
     ==> is_uint64 x_1
     ==> addr_le a_2 a_3
     ==> valid_rw t (shift a (&0:int)) ((&1:int) + x_1 + x_2)
     ==> (!i:int.
            (&0:int) <= i
            ==> i < x_1
            ==> ~(t_1 (shift a i) = (&0:int)))
     ==> (!i:int.
            (&0:int) <= i
            ==> i + SND a < SND a_2
            ==> ~(t_1 (shift a i) = (&0:int)))
     ==> p_valid_str t t_1 (shift a_2 (&1:int))`;;
