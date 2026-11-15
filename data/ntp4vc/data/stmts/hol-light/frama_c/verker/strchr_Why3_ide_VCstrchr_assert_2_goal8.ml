(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strchr_Why3_ide_VCstrchr_assert_2_goal8:
  a strchr verification condition asserting that the computed end of a valid
  C string is the current address exactly when the searched signed byte is
  zero, under the stated address-order, memory, search, and no-earlier-match
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_sint8 to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strchr:((int#int)->int)->(int#int)->int->(int#int).
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !i:int.
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
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
     let a_2 = shift a_1 (l_strlen t_1 a_1) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!p q:int#int.
            FST p = FST q
            ==> (addr_lt p q <=> SND p < SND q))
     ==> (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
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
     ==> (!mchar str c.
            (if mchar str = c
             then l_strchr mchar str c = str
             else if mchar str = (&0:int)
             then l_strchr mchar str c = ((&0:int),(&0:int))
             else
               l_strchr mchar (shift str (&1:int)) c =
               l_strchr mchar str c))
     ==> x = to_sint8 i
     ==> l_strchr t_1 a_1 x = l_strchr t_1 a x
     ==> (addr_lt a a_2 <=> ~(x = (&0:int)))
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_sint32 i
     ==> addr_le a_1 a
     ==> is_sint8 x
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> addr_le a a_2
     ==> (!a_3:int#int.
            addr_lt a_3 a
            ==> addr_le a_1 a_3
            ==> ~(x = t_1 a_3))
     ==> (a_2 = a <=> x = (&0:int))`;;
