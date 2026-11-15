(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strnchr_Why3_ide_VCstrnchr_loop_inv_4_preserved_goal5:
  preservation of a bounded string-search loop invariant, concluding that
  advancing the current address by one byte yields a valid bounded string
  segment, under the stated memory, address-order, integer-range,
  bounded-string-length, and no-earlier-match assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_sint8 to_uint64:int->int.
   !l_strnlen:((int#int)->int)->(int#int)->int->int.
   !t_1:(int#int)->int.
   !a:int#int.
   !i_1:int.
   !a_1:int#int.
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
     let x = t_1 a in
     let x_1 = to_sint8 i_1 in
     let x_2 = SND a_1 in
     let x_3 = i + x_2 in
     let x_4 = SND a in
     let x_6 = i + x_2 - x_4 in
     let x_7 = l_strnlen t_1 a_1 i in
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
     ==> ~(x = (&0:int))
     ==> ~(x = x_1)
     ==> ~(x_3 = x_4)
     ==> x_4 + l_strnlen t_1 a x_6 = x_2 + x_7
     ==> x_2 <= x_4
     ==> region (FST a_1) <= (&0:int)
     ==> x_4 <= x_3
     ==> linked t
     ==> sconst t_1
     ==> is_sint32 i_1
     ==> is_uint64 i
     ==> addr_le a_1 a
     ==> is_sint8 x
     ==> p_valid_strn t t_1 a_1 i
     ==> is_uint64 x_6
     ==> addr_le a (shift a_1 x_7)
     ==> p_valid_strn t t_1 a x_6
     ==> (!a_2:int#int.
            addr_lt a_2 a
            ==> addr_le a_1 a_2
            ==> ~(t_1 a_2 = x_1))
     ==> p_valid_strn
           t
           t_1
           (shift a (&1:int))
           (to_uint64 (i + x_2 - (&1:int) - x_4))`;;
