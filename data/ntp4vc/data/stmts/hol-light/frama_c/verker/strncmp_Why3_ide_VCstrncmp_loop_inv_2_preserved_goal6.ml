(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_2_preserved_goal6:
  preservation of a strncmp loop invariant, concluding that the one-byte
  successor of the second current address lies between the first current
  address and its bounded logical string end, under the stated memory,
  address-order, byte-range, valid-string, offset, and prefix-equality
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint8 to_uint64:int->int.
   !l_strnlen:((int#int)->int)->(int#int)->int->int.
   !t_1:(int#int)->int.
   !a_2 a_3 a_1 a:int#int.
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
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint64 =
       \z:int.
         (&0:int) <= z /\ z < (&18446744073709551616:int) in
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
     let x = t_1 a_2 in
     let x_1 = to_uint8 x in
     let x_2 = t_1 a_3 in
     let x_3 = SND a_1 in
     let x_4 = SND a_3 in
     let x_5 = SND a in
     let x_6 = SND a_2 in
     let x_7 = x_4 - x_5 in
     let x_8 = t_1 (shift a_1 x_7) in
     let x_9 = t_1 (shift a x_7) in
     let x_10 = i + x_6 - x_3 in
     let x_11 = l_strnlen t_1 a x_10 in
     let x_12 = l_strnlen t_1 a_1 x_10 in
     let a_4 = shift a x_11 in
     let a_5 = shift a_3 (&1:int) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!z:int. is_uint8 (to_uint8 z))
     ==> (!z:int. is_uint8 z ==> to_uint8 z = z)
     ==> (!z:int. to_uint8 (to_uint8 z) = to_uint8 z)
     ==> (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!z:int. to_uint64 (to_uint64 z) = to_uint64 z)
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
     ==> ~(i = (&0:int))
     ==> ~(x_1 = (&0:int))
     ==> to_uint8 x_2 = x_1
     ==> x_3 + x_4 = x_5 + x_6
     ==> x_8 = x_9
     ==> x_5 + x_11 = x_4 + l_strnlen t_1 a_3 i
     ==> x_3 + x_12 = x_6 + l_strnlen t_1 a_2 i
     ==> (&0:int) <= i
     ==> x_3 <= x_6
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint64 i
     ==> addr_le a a_3
     ==> addr_le a_1 a_2
     ==> is_sint8 x
     ==> is_sint8 x_2
     ==> p_valid_strn t t_1 a_2 i
     ==> p_valid_strn t t_1 a_3 i
     ==> is_uint64 x_10
     ==> is_sint8 x_9
     ==> is_sint8 x_8
     ==> p_valid_strn t t_1 a x_10
     ==> p_valid_strn t t_1 a_1 x_10
     ==> addr_le a_2 (shift a_1 x_12)
     ==> addr_le a_3 a_4
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 + x_3 < x_6
            ==> t_1 (shift a_1 i_1) = t_1 (shift a i_1))
     ==> (!i_1:int.
            let x_13 = t_1 (shift a_1 i_1) in
            let x_14 = t_1 (shift a i_1) in
            (&0:int) <= i_1
            ==> i_1 < x_11
            ==> (to_uint8 x_13 = to_uint8 x_14 <=> x_13 = x_14))
     ==> addr_le a a_5 /\ addr_le a_5 a_4`;;
