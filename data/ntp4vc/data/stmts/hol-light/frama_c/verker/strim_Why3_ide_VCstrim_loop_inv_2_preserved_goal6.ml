(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_loop_inv_2_preserved_goal6:
  preservation of a string-trimming loop invariant, concluding that the byte
  read from the source memory at the second address is whitespace, under
  the stated string, memory, address-order, integer-range, nonzero-byte, and
  intervening-whitespace assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !i:int.
   !t:int->int.
   !a_2:int#int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
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
     let p_isspace =
       \c:int.
         c = (&9:int) \/
         c = (&10:int) \/
         c = (&12:int) \/
         c = (&13:int) \/
         c = (&32:int) in
     let x = l_strlen t_1 a in
     let a_3 = shift a (x - (&1:int)) in
     let x_1 = t_1 a_3 in
     let x_2 = t_1 a_1 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!p q:int#int.
            FST p = FST q
            ==> (addr_lt p q <=> SND p < SND q))
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
     ==> ~(i = (&0:int))
     ==> ~(x = (&0:int))
     ==> t_1 (shift a x) = (&0:int)
     ==> ~(x_1 = (&0:int))
     ==> (&0:int) < x
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint8 i
     ==> addr_le a a_1
     ==> is_sint8 x_2
     ==> p_isspace x_2
     ==> p_valid_str t t_1 a
     ==> is_uint64 x
     ==> addr_lt (shift a_1 (--(&1:int))) a_2
     ==> addr_le (shift a (--(&1:int))) a_1
     ==> addr_le a_1 a_3
     ==> addr_le a_2 a_3
     ==> is_sint8 x_1
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < x
            ==> ~(t_1 (shift a i_1) = (&0:int)))
     ==> (!a_4:int#int.
            addr_lt a_1 a_4
            ==> addr_le a_4 a_3
            ==> p_isspace (t_1 a_4))
     ==> p_isspace (t_1 a_2)`;;
