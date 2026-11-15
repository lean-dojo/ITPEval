(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_8_established_goal15:
  establishment of a strspn loop invariant concluding that the byte at a
  selected acceptance-string address differs from the current nonzero signed
  byte, under the stated memory, address-order, string-validity, span-length,
  and prior-match assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strspn:(int#int)->(int#int)->int.
   !t_1:(int#int)->int.
   !a_1 a a_3:int#int.
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
         ?i:int.
           mchar (shift s i) = (&0:int) /\
           is_uint64 i /\
           valid_rw malloc (shift s (&0:int)) ((&1:int) + i) /\
           (!j:int.
              j <= i
              ==> is_sint8 (mchar (shift s j))) in
     let p_in_array =
       \(mchar:(int#int)->int)
        (s:int#int)
        (c:int).
         ?p:int#int.
           mchar p = c /\
           addr_le s p /\
           addr_lt p (shift s (l_strlen mchar s)) in
     let x = t_1 a_1 in
     let x_1 = SND a_1 in
     let x_2 = SND a in
     let x_3 = l_strlen t_1 a in
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
     ==> (!mchar s accept.
            mchar s = (&0:int)
            ==> l_strspn s accept = (&0:int))
     ==> (!mchar s accept.
            ~(mchar s = (&0:int))
            ==> ~(p_in_array mchar accept (mchar s))
            ==> l_strspn s accept = (&0:int))
     ==> (!mchar s accept.
            ~(mchar s = (&0:int))
            ==> p_in_array mchar accept (mchar s)
            ==> (&1:int) + l_strspn (shift s (&1:int)) accept =
                l_strspn s accept)
     ==> ~(x = (&0:int))
     ==> x_1 + l_strspn a_1 a_3 = x_2 + l_strspn a a_3
     ==> x_2 <= x_1
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> x_1 <= x_2 + x_3
     ==> linked t
     ==> sconst t_1
     ==> addr_lt a_2 a_3
     ==> addr_le a a_1
     ==> addr_le a_3 a_2
     ==> is_sint8 x
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> p_valid_str t t_1 a_3
     ==> is_uint64 (x_1 - x_2)
     ==> addr_le a_1 (shift a x_3)
     ==> (!a_4:int#int.
            addr_lt a_4 a_1
            ==> addr_le a a_4
            ==> (?a_5:int#int.
                   t_1 a_4 = t_1 a_5 /\
                   addr_le a_3 a_5 /\
                   addr_lt a_5
                     (shift a_3 (l_strlen t_1 a_3))))
     ==> ~(t_1 a_2 = x)`;;
