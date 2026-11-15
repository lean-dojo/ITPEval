(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_exists_post_goal7:
  a match-string postcondition verification condition identifying the returned
  match index under the stated memory, integer-range, string-validity, and
  preceding-entry assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !to_sint8 to_uint8 to_sint64 to_uint64:int->int.
   !l_strlen:((int#int)->int)->(int#int)->int.
   !l_strncmp:((int#int)->int)->(int#int)->(int#int)->int->int.
   !l_real_len:((int#int)->(int#int))->(int#int)->int->int.
   !l_match_string:
      ((int#int)->(int#int))->
      ((int#int)->int)->
      (int#int)->int->(int#int)->int.
   !t_2:(int#int)->(int#int).
   !a_1:int#int.
   !i i_1:int.
   !t_1:(int#int)->int.
   !i_3:int.
   !a:int#int.
   !i_2:int.
   !t:int->int.
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_sint64 =
       \z:int.
         --(&9223372036854775808:int) <= z /\
         z < (&9223372036854775808:int) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
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
     let l_cmp =
       \u v:int.
         if v = u then (&0:int)
         else if u < v then --(&1:int)
         else (&1:int) in
     let l_strcmp =
       \(mchar:(int#int)->int) (cs:int#int) (ct:int#int).
         l_strncmp mchar cs ct (l_strlen mchar cs) in
     let x = l_real_len t_2 a_1 i in
     let a_2 = t_2 (shift a_1 i_1) in
     let a_3 = shift a_1 (&0:int) in
     (!z:int. is_sint8 (to_sint8 z))
     ==> (!z:int. is_sint8 z ==> to_sint8 z = z)
     ==> (!z:int. is_uint8 (to_uint8 z))
     ==> (!z:int. is_uint8 z ==> to_uint8 z = z)
     ==> (!z:int. to_sint8 (to_uint8 z) = to_sint8 z)
     ==> (!z:int. is_sint64 (to_sint64 z))
     ==> (!z:int. is_sint64 z ==> to_sint64 z = z)
     ==> (!z:int. is_uint64 (to_uint64 z))
     ==> (!z:int. is_uint64 z ==> to_uint64 z = z)
     ==> (!z:int. to_sint64 (to_uint64 z) = to_sint64 z)
     ==> (!mchar s.
            (if mchar (shift s (&0:int)) = (&0:int)
             then l_strlen mchar s = (&0:int)
             else
               to_uint64
                 ((&1:int) + l_strlen mchar (shift s (&1:int))) =
               l_strlen mchar s))
     ==> (!mchar s. is_uint64 (l_strlen mchar s))
     ==> (!mchar cs ct n.
            (if n = --(&1:int)
             then l_strncmp mchar cs ct n = (&0:int)
             else if mchar (shift ct (&0:int)) =
                     mchar (shift cs (&0:int))
             then
               l_strncmp mchar (shift cs (&1:int)) (shift ct (&1:int))
                 (n - (&1:int)) =
               l_strncmp mchar cs ct n
             else
               l_cmp (to_uint8 (mchar (shift cs (&0:int))))
                 (to_uint8 (mchar (shift ct (&0:int)))) =
               l_strncmp mchar cs ct n))
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
     ==> (!mptr mchar p n s.
            (if n = (&0:int)
             then l_match_string mptr mchar p n s = (&0:int)
             else if
               l_strcmp mchar (mptr (shift p (&0:int))) s = (&0:int)
             then l_match_string mptr mchar p n s = (&0:int)
             else
               l_match_string mptr mchar (shift p (&1:int))
                 (to_uint64 (n - (&1:int))) s =
               l_match_string mptr mchar p n s))
     ==> (!mptr mchar p n s.
            is_uint64 (l_match_string mptr mchar p n s))
     ==> l_strcmp t_1 (t_2 (shift a_1 i_3)) a = (&0:int)
     ==> (&0:int) <= i_2
     ==> (&0:int) <= i_3
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> x <= i
     ==> i_3 < x
     ==> i_2 <= x
     ==> i <= (&2147483647:int)
     ==> framed t_2
     ==> linked t
     ==> sconst t_1
     ==> is_sint32 i_2
     ==> is_uint64 i
     ==> is_uint64 i_3
     ==> p_valid_str t t_1 a
     ==> (if to_uint64 i_2 < i
          then
            if t_2 (shift a_1 i_2) = ((&0:int),(&0:int))
            then i_1 = --(&22:int)
            else
              i_2 = i_1 /\
              l_strcmp t_1 a_2 a = (&0:int) /\
              p_valid_str t t_1 a_2 /\
              (!i_4:int.
                 t_1 (shift a_2 i_4) = t_1 (shift a i_4) \/
                 i_4 < (&0:int) \/
                 l_strlen t_1 a_2 < i_4)
          else i_1 = --(&22:int))
     ==> (x = i ==> valid_rw t a_3 i)
     ==> (x < i ==> valid_rw t a_3 ((&1:int) + x))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < i_2
            ==> p_valid_str t t_1 (t_2 (shift a_1 i_4)))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < i_2
            ==> ~(l_strcmp t_1 (t_2 (shift a_1 i_4)) a = (&0:int)))
     ==> (!i_4:int.
            (&0:int) <= i_4
            ==> i_4 < x
            ==> is_uint64 i_4
            ==> p_valid_str t t_1 (t_2 (shift a_1 i_4)))
     ==> l_match_string t_2 t_1 a_1 x a = i_1`;;
