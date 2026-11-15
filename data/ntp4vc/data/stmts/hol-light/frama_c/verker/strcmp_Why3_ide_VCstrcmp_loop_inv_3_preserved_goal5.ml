(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_3_preserved_goal5:
  preservation of a strcmp loop invariant, concluding that the one-byte
  successor of the current address lies between the first string's start and
  logical end under the stated memory, string, byte, offset, and prefix
  equality assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint8 to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strncmp:((int#int)->int)->(int#int)->(int#int)->int->int.
   !t_1:(int#int)->int.
   !a a_2 a_3 a_1:int#int.
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
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
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
     let l_cmp =
       \u v:int.
         if v = u then (&0:int)
         else if u < v then --(&1:int)
         else (&1:int) in
     let l_strcmp =
       \(mchar:(int#int)->int) (cs:int#int) (ct:int#int).
         l_strncmp mchar cs ct (l_strlen mchar cs) in
     let x = t_1 a in
     let x_1 = to_uint8 x in
     let x_2 = t_1 a_2 in
     let x_3 = SND a_2 in
     let x_4 = SND a_3 in
     let x_5 = l_strlen t_1 a_3 in
     let x_6 = x_3 - x_4 in
     let x_7 = t_1 (shift a_3 x_6) in
     let x_8 = t_1 (shift a_1 x_6) in
     let a_4 = shift a_1 (l_strlen t_1 a_1) in
     let a_5 = shift a (&1:int) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_uint8 (to_uint8 z))
     ==> (!z:int. is_uint8 z ==> to_uint8 z = z)
     ==> (!z:int. to_uint8 (to_uint8 z) = to_uint8 z)
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
     ==> (!mchar cs ct n.
            (if n = --(&1:int)
             then l_strncmp mchar cs ct n = (&0:int)
             else if mchar (shift ct (&0:int)) =
                     mchar (shift cs (&0:int))
             then
               l_strncmp mchar (shift cs (&1:int)) (shift ct (&1:int))
                 (n - (&1:int)) =
               l_strncmp mchar cs ct n
             else
               l_cmp (to_uint8 (mchar (shift cs (&0:int))))
                 (to_uint8 (mchar (shift ct (&0:int)))) =
               l_strncmp mchar cs ct n))
     ==> ~(x_1 = (&0:int))
     ==> to_uint8 x_2 = x_1
     ==> l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a
     ==> SND a_1 + x_3 = SND a + x_4
     ==> x_4 + x_5 = x_3 + l_strlen t_1 a_2
     ==> x_7 = x_8
     ==> ((!i:int.
             (&0:int) <= i
             ==> i <= x_5
             ==> to_uint8 (t_1 (shift a_3 i)) =
                 to_uint8 (t_1 (shift a_1 i)))
          <=>
          (!i:int.
             (&0:int) <= i
             ==> i <= x_5
             ==> t_1 (shift a_3 i) = t_1 (shift a_1 i)))
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> addr_le a_1 a
     ==> addr_le a_3 a_2
     ==> is_sint8 x
     ==> is_sint8 x_2
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> p_valid_str t t_1 a_2
     ==> p_valid_str t t_1 a_3
     ==> addr_le a a_4
     ==> addr_le a_2 (shift a_3 x_5)
     ==> is_sint8 x_8
     ==> is_sint8 x_7
     ==> (!i:int.
            (&0:int) <= i
            ==> i + x_4 < x_3
            ==> t_1 (shift a_3 i) = t_1 (shift a_1 i))
     ==> addr_le a_1 a_5 /\ addr_le a_5 a_4`;;
