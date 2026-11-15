(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23:
  a strncmp length-difference postcondition verification condition concluding
  that the signed comparison result is one, under the stated memory,
  address-order, bounded-string validity, character-equality, integer-range,
  and logical string-length assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint8 to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strnlen:((int#int)->int)->(int#int)->int->int.
   !a_1 a_2 a a_3:int#int.
   !i_1:int.
   !t_1:(int#int)->int.
   !t:int->int.
   !i_2 i_3 i:int.
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
     let p_valid_strn =
       \(malloc:int->int)
        (mchar:(int#int)->int)
        (s:int#int)
        (cnt:int).
         valid_rw malloc (shift s (&0:int)) ((&1:int) + cnt) \/
         ((?n:int.
             mchar (shift s n) = (&0:int) /\
             n < cnt /\
             is_uint64 n /\
             valid_rw malloc (shift s (&0:int)) ((&1:int) + n)) /\
          (!j:int.
             j <= cnt
             ==> is_sint8 (mchar (shift s j)))) in
     let x = SND a_1 in
     let x_1 = SND a_2 in
     let x_2 = SND a in
     let x_3 = SND a_3 in
     let x_4 = i_1 + x - x_2 in
     let x_5 = l_strnlen t_1 a_1 i_1 in
     let x_6 = x + x_5 in
     let x_7 = l_strnlen t_1 a_3 i_1 in
     let x_8 = i_1 + x in
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
     ==> (!mchar s cnt.
            (if cnt = (&0:int) \/
                mchar (shift s (&0:int)) = (&0:int)
             then l_strnlen mchar s cnt = (&0:int)
             else
               to_uint64
                 ((&1:int) +
                  l_strnlen
                    mchar
                    (shift s (&1:int))
                    (to_uint64 (cnt - (&1:int)))) =
               l_strnlen mchar s cnt))
     ==> (!mchar s cnt. is_uint64 (l_strnlen mchar s cnt))
     ==> x + x_1 = x_2 + x_3
     ==> x_2 + l_strnlen t_1 a x_4 = x_6
     ==> x_1 + l_strnlen t_1 a_2 x_4 = x_3 + x_7
     ==> (&0:int) < i_1
     ==> x <= x_2
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> x_5 < x_7
     ==> x_2 <= x_8
     ==> linked t
     ==> sconst t_1
     ==> is_uint8 i_2
     ==> is_uint8 i_3
     ==> is_sint32 i
     ==> is_uint64 i_1
     ==> addr_le a_1 a
     ==> addr_le a_3 a_2
     ==> p_valid_strn t t_1 a_1 i_1
     ==> p_valid_strn t t_1 a_3 i_1
     ==> is_uint64 x_4
     ==> addr_le a (shift a_1 x_5)
     ==> addr_le a_2 (shift a_3 x_7)
     ==> p_valid_strn t t_1 a x_4
     ==> p_valid_strn t t_1 a_2 x_4
     ==> (if x_8 = x_2
          then i = (&0:int)
          else
            to_uint8 (t_1 a) = i_2 /\
            to_uint8 (t_1 a_2) = i_3 /\
            (if i_3 = i_2
             then i = (&0:int) /\ i_3 = (&0:int)
             else if i_3 < i_2
             then i = --(&1:int)
             else i = (&1:int)) /\
            (i_2 = (&0:int)
             ==> x_5 = l_strlen t_1 a_1 /\
                 x_6 = x_2 /\
                 p_valid_str t t_1 a_1) /\
            (i_3 = (&0:int)
             ==> x_7 = l_strlen t_1 a_3 /\
                 x + x_7 = x_2 /\
                 p_valid_str t t_1 a_3))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < x_7
            ==> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 + x < x_2
            ==> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4))
     ==> (!i_4:int.
            let x_9 = t_1 (shift a_3 i_4) in
            let x_10 = t_1 (shift a_1 i_4) in
            (&0:int) <= i_4
            ==> i_4 < x_7
            ==> (to_uint8 x_9 = to_uint8 x_10 <=> x_9 = x_10))
     ==> i = (&1:int)`;;
