(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlen_Why3_ide_VCstrlen_post_2_goal1:
  a strlen postcondition verification condition concluding that the byte at
  the shifted initial address corresponding to the current pointer offset is
  zero, under the stated memory, string-validity, address-order, byte-range,
  and string-length assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !a_1:int#int.
   !t_1:(int#int)->int.
   !a:int#int.
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
     let x = SND a_1 in
     let x_1 = l_strlen t_1 a_1 in
     let x_2 = SND a in
     let x_3 = t_1 (shift a_1 (to_uint64 (x_2 - x))) in
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
     ==> t_1 a = (&0:int)
     ==> x + x_1 = x_2 + l_strlen t_1 a
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> addr_le a_1 a
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> addr_le a (shift a_1 x_1)
     ==> is_sint8 x_3
     ==> x_3 = (&0:int)`;;
