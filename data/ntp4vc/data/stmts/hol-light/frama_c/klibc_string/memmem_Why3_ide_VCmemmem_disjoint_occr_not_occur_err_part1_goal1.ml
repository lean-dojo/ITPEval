(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/memmem_Why3_ide_VCmemmem_disjoint_occr_not_occur_err_part1_goal1:
  a memmem disjoint-occurrence error-path verification condition asserting
  the stated zero-size and size-order alternatives, or the existence of a
  nonnegative offset giving source/destination memory equality throughout the
  relevant index interval, under the given region, linking, unsigned-range,
  memory-validity, and separation assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_2 a_3:int#int.
   !i i_1:int.
   !t:int->int.
   !t_1:(int#int)->int.
   !a_1 a:int#int.
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
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let a_4 = shift a_2 (&0:int) in
     let a_5 = shift a_3 (&0:int) in
     (&0:int) <= i
     ==> (&0:int) <= i_1
     ==> region (FST a_2) <= (&0:int)
     ==> region (FST a_3) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> valid_rw t a_4 i_1
     ==> valid_rw t a_5 i
     ==> separated a_5 i a_4 i_1
     ==> i = (&0:int) \/
         i_1 = (&0:int) \/
         i < i_1 \/
         (~(i = (&0:int)) /\
          ~(i_1 = (&0:int)) /\
          i_1 <= i) \/
         (?i_2:int.
            (&0:int) <= i_2 /\
            i_2 + i_1 <= i /\
            (!i_3:int.
               t_1 (shift a_1 (i_3 + i_2)) = t_1 (shift a i_3) \/
               i_3 < (&0:int) \/
               i_1 <= i_3))`;;
