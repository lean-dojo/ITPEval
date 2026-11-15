(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strlcpy_Why3_ide_VCstrlcpy_assert_3_goal4:
  a strlcpy verification condition concluding that the null-terminated,
  updated destination memory has string length equal to the copy index, under
  the stated address-region, memory-validity, unsigned-range, source-string,
  destination-string, termination, and copied-prefix assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !a_1 a:int#int.
   !t_2 t_1:(int#int)->int.
   !i_1 i:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
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
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
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
     let x = FST a_1 in
     let x_1 = FST a in
     let x_2 = l_strlen t_2 a in
     let a_2 = shift a_1 (&0:int) in
     let a_3 = havoc t_1 t_2 a_2 i_1 in
     let a_4 = update a_3 (shift a_1 i_1) (&0:int) in
     (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!mchar s.
            (if mchar (shift s (&0:int)) = (&0:int)
             then l_strlen mchar s = (&0:int)
             else
               to_uint64
                 ((&1:int) + l_strlen mchar (shift s (&1:int))) =
               l_strlen mchar s))
     ==> (!mchar s. is_uint64 (l_strlen mchar s))
     ==> ~(i = (&0:int))
     ==> ~(x = x_1)
     ==> t_2 (shift a x_2) = (&0:int)
     ==> region x_1 <= (&0:int)
     ==> region x <= (&0:int)
     ==> linked t
     ==> sconst t_2
     ==> is_uint64 i
     ==> is_uint64 i_1
     ==> p_valid_str t t_2 a
     ==> is_uint64 x_2
     ==> valid_rd t (shift a (&0:int)) i_1
     ==> valid_rw t a_2 i
     ==> valid_rw t a_2 i_1
     ==> p_valid_str t a_4 a_1
     ==> (if i <= x_2
          then to_uint64 (i - (&1:int)) = i_1
          else x_2 = i_1)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < x_2
            ==> ~(t_2 (shift a i_2) = (&0:int)))
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < i_1
            ==> a_3 (shift a_1 i_2) = a_3 (shift a i_2))
     ==> l_strlen a_4 a_1 = i_1`;;
