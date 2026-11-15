(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncat_Why3_ide_VCstrncat_loop_inv_2_preserved_goal4:
  preservation of a bounded string-concatenation loop invariant, concluding
  that advancing the current source address by one byte yields a valid
  string, under the stated memory, address-order, integer-range, string
  validity, and null-character assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strnlen:((int#int)->int)->(int#int)->int->int.
   !t_1:(int#int)->int.
   !a_2 a a_1:int#int.
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
     let x = t_1 a_2 in
     let x_1 = l_strlen t_1 a in
     let a_3 = shift a x_1 in
     let x_2 = l_strnlen t_1 a_1 i in
     let x_3 = t_1 (shift a_1 x_2) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
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
     ==> ~(i = (&0:int))
     ==> ~(x = (&0:int))
     ==> t_1 a_3 = (&0:int)
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> i + x_1 <= (&18446744073709551615:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint64 i
     ==> addr_le a a_2
     ==> is_sint8 x
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_2
     ==> is_uint64 x_1
     ==> p_valid_strn t t_1 a_1 i
     ==> is_uint64 x_2
     ==> addr_le a_2 a_3
     ==> is_sint8 x_3
     ==> valid_rw t (shift a (&0:int)) ((&1:int) + i + x_1)
     ==> ((!i_1:int.
            (&0:int) <= i_1
            ==> i_1 <= i
            ==> ~(t_1 (shift a_1 i_1) = (&0:int)))
          ==> x_2 = i)
     ==> ((?i_1:int.
            t_1 (shift a_1 i_1) = (&0:int) /\
            (&0:int) <= i_1 /\
            i_1 <= i)
          ==> x_3 = (&0:int))
     ==> ((?i_1:int.
            t_1 (shift a_1 i_1) = (&0:int) /\
            (&0:int) <= i_1 /\
            i_1 <= i)
          ==> (!i_1:int.
                 (&0:int) <= i_1
                 ==> i_1 < x_2
                 ==> ~(t_1 (shift a_1 i_1) = (&0:int))))
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < x_1
            ==> ~(t_1 (shift a i_1) = (&0:int)))
     ==> p_valid_str t t_1 (shift a_2 (&1:int))`;;
