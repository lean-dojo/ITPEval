(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_preserved_goal2:
  preservation of a sysfs string-equality loop invariant, concluding that
  the successor of the current unsigned 64-bit index is unchanged by the
  unsigned conversion under the stated memory, string-validity, byte, and
  bounded-prefix equality assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !to_uint64 to_sint32:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strncmp_2:((int#int)->int)->(int#int)->(int#int)->int->int.
   !a_1:int#int.
   !i:int.
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
     let p_strnequal =
       \(mchar:(int#int)->int)
        (s1:int#int)
        (s2:int#int)
        (n:int).
         l_strncmp_2 mchar s1 s2 n = (&0:int) in
     let a_2 = shift a_1 i in
     let x = t_1 a_2 in
     let a_3 = shift a i in
     let x_1 = t_1 a_3 in
     let x_2 = (&1:int) + i in
     (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!z:int. to_uint64 (to_uint64 z) = to_uint64 z)
     ==> (!z:int. is_sint32 (to_sint32 z))
     ==> (!z:int. is_sint32 z ==> to_sint32 z = z)
     ==> (!z:int. to_sint32 (to_sint32 z) = to_sint32 z)
     ==> (!mchar s.
            (if mchar (shift s (&0:int)) = (&0:int)
             then l_strlen mchar s = (&0:int)
             else
               to_uint64
                 ((&1:int) + l_strlen mchar (shift s (&1:int))) =
               l_strlen mchar s))
     ==> (!mchar s. is_uint64 (l_strlen mchar s))
     ==> (!mchar s1 s2 n.
            (if n = (&0:int)
             then l_strncmp_2 mchar s1 s2 n = (&0:int)
             else if mchar (shift s2 (&0:int)) =
                     mchar (shift s1 (&0:int))
             then
               if mchar (shift s1 (&0:int)) = (&0:int)
               then l_strncmp_2 mchar s1 s2 n = (&0:int)
               else
                 l_strncmp_2
                   mchar
                   (shift s1 (&1:int))
                   (shift s2 (&1:int))
                   (to_uint64 (n - (&1:int))) =
                 l_strncmp_2 mchar s1 s2 n
             else
               to_sint32
                 (mchar (shift s1 (&0:int)) -
                  mchar (shift s2 (&0:int))) =
               l_strncmp_2 mchar s1 s2 n))
     ==> (!mchar s1 s2 n.
            is_sint32 (l_strncmp_2 mchar s1 s2 n))
     ==> ~(x = (&0:int))
     ==> x = x_1
     ==> i <= l_strlen t_1 a
     ==> i <= l_strlen t_1 a_1
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint64 i
     ==> p_valid_str t t_1 a
     ==> p_valid_str t t_1 a_1
     ==> p_strnequal t_1 a_1 a i
     ==> is_sint8 x_1
     ==> is_sint8 x
     ==> p_valid_str t t_1 a_3
     ==> p_valid_str t t_1 a_2
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < i
            ==> t_1 (shift a_1 i_1) = t_1 (shift a i_1))
     ==> x_2 = to_uint64 x_2`;;
