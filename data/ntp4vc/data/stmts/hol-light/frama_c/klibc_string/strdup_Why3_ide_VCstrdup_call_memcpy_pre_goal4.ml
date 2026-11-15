(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4:
  a strdup-to-memcpy call-precondition verification condition asserting
  separation of the source string and destination ranges of the converted
  string length, under the stated nonnull, memory-region, linking, constancy,
  string-length, signed-range, and destination-validity assumptions. This
  file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !l_length:((int#int)->int)->(int#int)->int.
   !to_uint32:int->int.
   !t_1:(int#int)->int.
   !a a_1:int#int.
   !t:int->int.
   !i i_1 i_2:int.
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
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let x = l_length t_1 a in
     let x_1 = (&1:int) + x in
     let x_2 = to_uint32 x_1 in
     let a_2 = shift a_1 (&0:int) in
     (!malloc mchar s n.
        p_length_of_str_is malloc mchar s n
        ==> l_length mchar s = n)
     ==> (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(((&0:int),(&0:int)) = a_1)
     ==> ~(x_2 = (&0:int))
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_sint32 x
     ==> p_length_of_str_is t t_1 a i
     ==> p_length_of_str_is t t_1 a i_1
     ==> p_length_of_str_is t t_1 a i_2
     ==> is_sint32 x_1
     ==> ((&0:int) < x_2 ==> valid_rw t a_2 x_2)
     ==> separated (shift a (&0:int)) x_2 a_2 x_2`;;
