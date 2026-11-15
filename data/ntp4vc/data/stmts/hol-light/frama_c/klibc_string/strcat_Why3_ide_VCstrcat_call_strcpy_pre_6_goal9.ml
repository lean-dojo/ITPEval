(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9:
  a strcat-to-strcpy call-precondition verification condition asserting
  separation of the address range beginning at a from the string range at
  a_1, under the stated string-length, memory-validity, address-order,
  linking, constancy, and null-character occurrence assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !l_length:((int#int)->int)->(int#int)->int.
   !to_sint8:int->int.
   !a_2:int#int.
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !t:int->int.
   !i i_3 i_1 i_2 i_4:int.
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
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let p_exists_first_occurence_of_char =
       \(malloc:int->int)
        (mchar:(int#int)->int)
        (s:int#int)
        (c:int)
        (pos:int).
         let char_value = to_sint8 c in
         let string_length = l_length mchar s in
         mchar (shift s pos) = char_value /\
         (&0:int) <= pos /\
         pos <= string_length /\
         --(&128:int) <= c /\
         c <= (&127:int) /\
         valid_rw malloc (shift s (&0:int))
           ((&1:int) + string_length) /\
         (!j:int.
            (&0:int) <= j
            ==> j < pos
            ==> ~(mchar (shift s j) = char_value)) in
     let x = FST a_2 in
     let x_1 = t_1 a in
     let a_3 = shift a_2 (&0:int) in
     let x_2 = l_length t_1 a_1 in
     let x_3 = l_length t_1 a_2 in
     let a_4 = shift a_1 (&0:int) in
     let x_4 = (&1:int) + x_2 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!malloc mchar s n.
           p_length_of_str_is malloc mchar s n
           ==> l_length mchar s = n)
     ==> (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> region (FST a_1) <= (&0:int)
     ==> region x <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_sint8 x_1
     ==> p_length_of_str_is t t_1 a_1 i
     ==> p_length_of_str_is t t_1 a_1 i_3
     ==> p_length_of_str_is t t_1 a_2 i_1
     ==> p_length_of_str_is t t_1 a_2 i_2
     ==> p_length_of_str_is t t_1 a_2 i_4
     ==> valid_rw t a_3 (x_2 + x_3)
     ==> separated a_3 ((&1:int) + x_3) a_4 x_4
     ==> ((!i_5:int.
            (&0:int) <= i_5
            ==> i_5 < x_3
            ==> ~(t_1 (shift a_2 i_5) = (&0:int)))
          ==> ((&0:int),(&0:int)) = a)
     ==> ((?i_5:int.
            t_1 (shift a_2 i_5) = (&0:int) /\
            (&0:int) <= i_5 /\
            i_5 < x_3)
          ==> x_1 = (&0:int))
     ==> ((?i_5:int.
            t_1 (shift a_2 i_5) = (&0:int) /\
            (&0:int) <= i_5 /\
            i_5 < x_3)
          ==> x = FST a)
     ==> ((?i_5:int.
            t_1 (shift a_2 i_5) = (&0:int) /\
            (&0:int) <= i_5 /\
            i_5 < x_3)
          ==> p_exists_first_occurence_of_char
                t t_1 a_2 (&0:int) (SND a - SND a_2))
     ==> ((?i_5:int.
            t_1 (shift a_2 i_5) = (&0:int) /\
            (&0:int) <= i_5 /\
            i_5 < x_3)
          ==> addr_le a_2 a /\
              addr_le a (shift a_2 x_3))
     ==> separated a_4 x_4 (shift a (&0:int)) x_4`;;
