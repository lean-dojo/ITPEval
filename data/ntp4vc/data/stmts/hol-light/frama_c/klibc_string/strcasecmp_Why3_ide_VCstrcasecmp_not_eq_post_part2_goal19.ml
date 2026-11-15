(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19:
  a strcasecmp non-equality postcondition verification condition asserting
  that the two strings cannot have equal uppercased bytes throughout the
  preceding address interval, under the stated string-length, memory,
  address-order, character-range, and case-conversion assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !l_length:((int#int)->int)->(int#int)->int.
   !to_uint8:int->int.
   !l_toupper:int->int.
   !a a_1 a_2:int#int.
   !t_1:(int#int)->int.
   !i_5 i_6:int.
   !t:int->int.
   !i i_1 i_4 i_2 i_3:int.
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
     let p_length_of_str_is =
       \(malloc:int->int)
        (mchar:(int#int)->int)
        (s:int#int)
        (n:int).
         mchar (shift s n) = (&0:int) /\
         (&0:int) <= n /\
         valid_rw malloc (shift s (&0:int)) ((&1:int) + n) /\
         (!j:int.
            (&0:int) <= j
            ==> j < n
            ==> ~(mchar (shift s j) = (&0:int))) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_is_lower =
       \c:int.
         (&97:int) <= c /\ c <= (&122:int) in
     let p_is_upper =
       \c:int.
         (&65:int) <= c /\ c <= (&90:int) in
     let x = FST a in
     let x_1 = SND a_1 in
     let x_2 = SND a in
     let a_3 = shift a_2 (x_1 - x_2) in
     let x_3 = t_1 a_1 in
     let x_4 = l_length t_1 a in
     let x_5 = l_length t_1 a_2 in
     let x_6 = to_uint8 x_3 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!malloc mchar s n.
           p_length_of_str_is malloc mchar s n
           ==> l_length mchar s = n)
     ==> (!z:int. is_uint8 (to_uint8 z))
     ==> (!z:int. is_uint8 z ==> to_uint8 z = z)
     ==> (!c:int. is_uint8 c ==> is_sint8 (l_toupper c))
     ==> (!c:int.
           is_uint8 c
           ==> p_is_lower c
           ==> (&32:int) + l_toupper c = c /\
               (!j:int.
                  is_uint8 j
                  ==> p_is_upper j
                  ==> l_toupper j = j /\
                      (!k:int.
                         is_uint8 k
                         ==> ~p_is_lower k
                         ==> ~p_is_upper k
                         ==> l_toupper k = k)))
     ==> FST a_1 = x
     ==> ~(l_toupper (to_uint8 (t_1 (shift a_2 i_5))) =
           l_toupper (to_uint8 (t_1 (shift a i_5))))
     ==> t_1 a_3 = (&0:int)
     ==> (&0:int) <= i_5
     ==> i_5 <= i_6
     ==> (&0:int) <= x_3
     ==> region x <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> x_3 <= (&255:int)
     ==> linked t
     ==> sconst t_1
     ==> is_sint32 i
     ==> addr_le a a_1
     ==> is_sint8 x_3
     ==> p_length_of_str_is t t_1 a i_1
     ==> p_length_of_str_is t t_1 a i_4
     ==> p_length_of_str_is t t_1 a i_6
     ==> p_length_of_str_is t t_1 a_2 i_2
     ==> p_length_of_str_is t t_1 a_2 i_3
     ==> p_length_of_str_is t t_1 a_2 i_6
     ==> addr_le a_1 (shift a x_4)
     ==> separated
           (shift a_2 (&0:int)) ((&1:int) + x_5)
           (shift a (&0:int)) ((&1:int) + x_4)
     ==> addr_le a_2 a_3
     ==> addr_le a_3 (shift a_2 x_5)
     ==> (p_is_lower (&0:int) ==> i = --(&32:int))
     ==> (p_is_upper (&0:int) ==> i = (&0:int))
     ==> (~p_is_lower (&0:int)
          ==> ~p_is_upper (&0:int)
          ==> i = (&0:int))
     ==> (p_is_upper x_6 ==> x_3 = i)
     ==> (p_is_lower x_6 ==> x_3 = (&32:int) + i)
     ==> (~p_is_lower x_6 ==> ~p_is_upper x_6 ==> x_3 = i)
     ==> ~(!i_7:int.
             (&0:int) <= i_7
             ==> i_7 + x_2 < x_1
             ==> l_toupper (to_uint8 (t_1 (shift a_2 i_7))) =
                 l_toupper (to_uint8 (t_1 (shift a i_7))) )`;;
