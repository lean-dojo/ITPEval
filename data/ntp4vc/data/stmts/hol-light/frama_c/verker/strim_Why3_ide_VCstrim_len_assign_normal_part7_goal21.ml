(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_len_assign_normal_part7_goal21:
  a string-trimming length-assignment normal-path verification condition
  concluding that the one-byte region following the inspected address is
  included in the original string buffer, under the stated string, memory,
  address-order, byte-range, and intervening-whitespace assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !p:bool.
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let included =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         (&0:int) < n
         ==> (&0:int) <= m /\
             FST p = FST q /\
             SND q <= SND p /\
             SND p + n <= SND q + m in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let invalid =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> malloc (FST p) <= SND p \/
             SND p + n <= (&0:int) in
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
     let p_isspace =
       \c:int.
         c = (&9:int) \/
         c = (&10:int) \/
         c = (&12:int) \/
         c = (&13:int) \/
         c = (&32:int) in
     let x = l_strlen t_1 a in
     let a_2 = shift a (x - (&1:int)) in
     let x_1 = t_1 a_2 in
     let x_2 = t_1 a_1 in
     let a_3 = shift a (--(&1:int)) in
     let a_4 = shift a_1 (&1:int) in
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
     ==> ~(x = (&0:int))
     ==> t_1 (shift a x) = (&0:int)
     ==> ~(x_1 = (&0:int))
     ==> (&0:int) < x
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_sint8 x_2
     ==> p_valid_str t t_1 a
     ==> is_uint64 x
     ==> addr_le a_3 a_1
     ==> ~(invalid t a_4 (&1:int))
     ==> addr_le a_1 a_2
     ==> is_sint8 x_1
     ==> (if addr_le a a_1
          then p = F /\ ~(p_isspace x_2)
          else a_3 = a_1 \/ ~(p_isspace x_2))
     ==> (!i:int.
            (&0:int) <= i
            ==> i < x
            ==> ~(t_1 (shift a i) = (&0:int)))
     ==> (!a_5:int#int.
            addr_lt a_1 a_5
            ==> addr_le a_5 a_2
            ==> p_isspace (t_1 a_5))
     ==> included a_4 (&1:int)
           (shift a (&0:int)) ((&1:int) + x)`;;
