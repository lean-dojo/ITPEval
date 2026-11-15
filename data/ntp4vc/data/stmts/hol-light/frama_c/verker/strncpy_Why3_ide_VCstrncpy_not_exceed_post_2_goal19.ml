(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19:
  a strncpy postcondition verification condition concluding bounded-string
  validity at the destination start address, under the stated memory-havoc,
  address-region, ordering, string-validity, range, writable-memory, and
  copied-prefix assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strnlen:((int#int)->int)->(int#int)->int->int.
   !a_3 a_1 a:int#int.
   !t_1 t_2 t_3:(int#int)->int.
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
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let is_uint64 =
       \z:int.
         (&0:int) <= z /\ z < (&18446744073709551616:int) in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
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
     let x = FST a_3 in
     let x_1 = FST a_1 in
     let a_4 = shift a_1 (&0:int) in
     let x_2 = SND a_1 in
     let x_3 = SND a in
     let x_4 = x_3 - x_2 in
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
     ==> ~(x = x_1)
     ==> havoc
           t_1 t_2 a_4
           ((&1:int) + l_strnlen t_3 a_3 (&0:int)) =
         t_3
     ==> x_2 <= x_3
     ==> region x_1 <= (&0:int)
     ==> region x <= (&0:int)
     ==> x_3 < x_2 + l_strlen t_2 a_3
     ==> linked t
     ==> sconst t_2
     ==> addr_le a_1 a
     ==> addr_le a_3 a_2
     ==> p_valid_str t t_2 a_3
     ==> p_valid_str t t_3 a_2
     ==> is_uint64 x_4
     ==> p_valid_strn t t_2 a_3 x_4
     ==> p_valid_strn t t_3 a x_4
     ==> addr_le a (shift a_1 x_4)
     ==> addr_le a_2 (shift a_3 (l_strnlen t_3 a_3 x_4))
     ==> valid_rw
           t a_4 ((&1:int) + l_strnlen t_2 a_3 x_4)
     ==> (!i:int.
            (&0:int) <= i
            ==> i + SND a_3 < SND a_2
            ==> t_3 (shift a_3 i) = t_3 (shift a_1 i))
     ==> p_valid_strn t t_3 a_1 x_4`;;
