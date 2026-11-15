(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/replace_copy/replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0:
  a replace-copy postcondition verification condition asserting that the
  specified conditional replacement behavior for a havoced destination memory
  is preserved when the hypotheses make its two range bounds equal, under the
  stated memory-validity, separation, linkage, unchanged-range, and
  integer-range assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a:int#int.
   !t_1 t_2:(int#int)->int.
   !i_2 i_3:int.
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
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_unchanged =
       \(m0:(int#int)->int) (m1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> m1 (shift base_addr j) =
               m0 (shift base_addr j) in
     let p_replace =
       \(m0:(int#int)->int) (m1:(int#int)->int)
        (source:int#int) (n:int) (destination:int#int)
        (old_value:int) (new_value:int).
         !j:int.
           (&0:int) <= j
           ==> j < n
           ==> (m1 (shift source j) = old_value
                ==> m0 (shift destination j) = new_value) /\
               (~(m1 (shift source j) = old_value)
                ==> m0 (shift destination j) =
                    m1 (shift source j)) in
     let a_2 = shift a_1 (&0:int) in
     let a_3 = shift a (&0:int) in
     let a_4 = havoc t_1 t_2 a_3 i_2 in
     i_3 <= i_2
     ==> (&0:int) <= i_3
     ==> i_2 <= i_3
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> valid_rd t a_2 i_2
     ==> valid_rw t a_3 i_2
     ==> separated a_2 i_2 a (&1:int)
     ==> p_unchanged a_4 t_2 a_1 i_3 i_2
     ==> p_replace a_4 t_2 a_1 i_3 a i_1 i
     ==> p_replace
           (havoc t_1 t_2 a_3 i_3) t_2 a_1 i_3 a i_1 i`;;
