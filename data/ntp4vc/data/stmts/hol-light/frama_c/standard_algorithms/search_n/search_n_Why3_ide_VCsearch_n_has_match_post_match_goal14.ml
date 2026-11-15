(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_has_match_post_match_goal14:
  a search_n match-post verification condition concluding that the reported
  interval is a constant range, under the stated C integer ranges, memory
  validity, existing-match, loop-state, and branch assumptions. This file
  contains no proof.
*)

let statement =
  `let shift =
     \(p:int#int) (k:int). (FST p,SND p + k) in
   let valid_rd =
     \(malloc:int->int) (p:int#int) (n:int).
       (&0:int) < n
       ==> ~((&0:int) = FST p) /\
           (&0:int) <= SND p /\
           SND p + n <= malloc (FST p) in
   let is_uint32 =
     \z:int.
       (&0:int) <= z /\ z < (&4294967296:int) in
   let is_sint32 =
     \z:int.
       --(&2147483648:int) <= z /\ z < (&2147483648:int) in
   let p_constantrange =
     \(mint:(int#int)->int) (base_addr:int#int)
      (first:int) (last:int) (value:int).
       !j:int.
         first <= j
         ==> j < last
         ==> mint (shift base_addr j) = value in
   let p_hasconstantsubrange =
     \(mint:(int#int)->int) (base_addr:int#int)
      (m:int) (n:int) (value:int).
       ?j:int.
         let endpoint = n + j in
         (&0:int) <= j /\
         endpoint <= m /\
         p_constantrange mint base_addr j endpoint value in
   !region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !t_1:(int#int)->int.
   !a:int#int.
   !i i_6 i_1 i_2:int.
   !t:int->int.
   !i_3 i_4 i_5 i_7:int.
     let x = t_1 (shift a (i - (&1:int))) in
     let x_1 = (&1:int) + i_6 in
     let x_2 = i_1 + i_2 in
     let a_1 = shift a i_6 in
     let x_3 = to_uint32 x_1 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (!z:int. to_uint32 (to_uint32 z) = to_uint32 z)
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_uint32 i_5
     ==> is_uint32 i_6
     ==> is_sint32 i_7
     ==> p_hasconstantsubrange t_1 a i_4 i_2 i_7
     ==> valid_rd t (shift a (&0:int)) i_4
     ==> is_sint32 x
     ==> (if (&0:int) < i_2
          then if i_2 <= i_4
               then i_5 = i_3 /\
                    i_5 = i_4 /\
                    i <= x_1 /\
                    p_constantrange t_1 a i i_6 i_7 /\
                    ~p_hasconstantsubrange t_1 a i_6 i_2 i_7 /\
                    (if i_6 < i_5
                     then i_1 = i /\
                          x_2 = x_1 /\
                          t_1 a_1 = i_7 /\
                          i_1 <= x_3 /\
                          i_6 <= (&4294967294:int) /\
                          x_3 <= (&4294967295:int) + i_1 /\
                          valid_rd t a_1 (&1:int)
                     else i_5 = i_1) /\
                    ((&0:int) < i ==> ~(x = i_7))
               else i_4 = i_1
          else i_1 = (&0:int))
     ==> p_constantrange t_1 a i_1 x_2 i_7`;;
