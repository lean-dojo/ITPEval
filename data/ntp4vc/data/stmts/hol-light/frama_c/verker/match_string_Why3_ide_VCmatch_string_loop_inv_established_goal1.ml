(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1:
  establishment of the match-string loop invariant that the logical real
  array length is nonnegative and at most the supplied unsigned bound, under
  the stated memory, framing, linkedness, and string-validity assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !to_uint64:int->int.
   !l_real_len:((int#int)->(int#int))->(int#int)->int->int.
   !t_2:(int#int)->(int#int).
   !a_1:int#int.
   !i:int.
   !a:int#int.
   !t:int->int.
   !t_1:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
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
     let x = l_real_len t_2 a_1 i in
     let a_2 = shift a_1 (&0:int) in
     (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!z:int. to_uint64 (to_uint64 z) = to_uint64 z)
     ==> (!mptr p n.
            (if n = (&0:int) \/
                mptr (shift p (&0:int)) = ((&0:int),(&0:int))
             then l_real_len mptr p n = (&0:int)
             else
               to_uint64
                 ((&1:int) +
                  l_real_len mptr (shift p (&1:int))
                    (to_uint64 (n - (&1:int)))) =
               l_real_len mptr p n))
     ==> (!mptr p n. is_uint64 (l_real_len mptr p n))
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> i <= (&2147483647:int)
     ==> framed t_2
     ==> linked t
     ==> sconst t_1
     ==> is_uint64 i
     ==> p_valid_str t t_1 a
     ==> (x = i ==> valid_rw t a_2 i)
     ==> (x < i ==> valid_rw t a_2 ((&1:int) + x))
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < x
            ==> is_uint64 i_1
            ==> p_valid_str t t_1 (t_2 (shift a_1 i_1)))
     ==> x <= i /\ (&0:int) <= x`;;
