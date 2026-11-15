(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/strreplace_Why3_ide_VCstrreplace_loop_inv_preserved_goal4:
  preservation of a string-replacement loop invariant, concluding that the
  one-byte successor of the current address is a valid string after the
  conditional character update, under the stated memory, address-order,
  byte-range, string-validity, and prefix-replacement assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le addr_lt:(int#int)->(int#int)->bool.
   !to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !t_2 t_1 t_3:(int#int)->int.
   !a_1 a:int#int.
   !t:int->int.
   !i i_1:int.
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
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
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
     let x = l_strlen t_2 a_1 in
     let a_2 = shift a_1 x in
     let a_3 = havoc t_1 t_2 (shift a_1 (&0:int)) x in
     let a_4 = a_3 a in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!p q:int#int.
            FST p = FST q
            ==> (addr_lt p q <=> SND p < SND q))
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
     ==> t_2 a_2 = (&0:int)
     ==> ~(a_4 = (&0:int))
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> sconst t_2
     ==> is_sint8 i
     ==> is_sint8 i_1
     ==> addr_le a_1 a
     ==> p_valid_str t t_2 a_1
     ==> is_uint64 x
     ==> addr_le a a_2
     ==> is_sint8 a_4
     ==> p_valid_str t a_3 a
     ==> p_valid_str t a_3 a_1
     ==> (if a_4 = i
          then update a_3 a i_1 = t_3
          else a_3 = t_3)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < x
            ==> ~(t_2 (shift a_1 i_2) = (&0:int)))
     ==> (!a_5:int#int.
            addr_le a a_5
            ==> addr_lt a_5 a_2
            ==> a_3 a_5 = t_2 a_5)
     ==> (!a_5:int#int.
            t_2 a_5 = i
            ==> addr_lt a_5 a
            ==> addr_le a_1 a_5
            ==> a_3 a_5 = i_1)
     ==> (!a_5:int#int.
            ~(t_2 a_5 = i)
            ==> addr_lt a_5 a
            ==> addr_le a_1 a_5
            ==> a_3 a_5 = t_2 a_5)
     ==> p_valid_str t t_3 (shift a (&1:int))`;;
