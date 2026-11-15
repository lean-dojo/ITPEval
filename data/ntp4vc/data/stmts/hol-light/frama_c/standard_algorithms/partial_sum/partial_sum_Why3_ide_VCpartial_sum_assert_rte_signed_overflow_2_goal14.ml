(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sum/partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14:
  the signed 32-bit upper-overflow verification condition for one partial-sum
  accumulation step under the stated memory, range, and prefix-sum invariants.
  This file contains no proof.
*)

let statement =
  `let shift =
     \(p:int#int) (k:int). (FST p,SND p + k) in
   let valid_rw =
     \(m:int->int) (p:int#int) (n:int).
       (&0:int) < n
       ==> (&0:int) < FST p /\
           (&0:int) <= SND p /\
           SND p + n <= m (FST p) in
   let valid_rd =
     \(m:int->int) (p:int#int) (n:int).
       (&0:int) < n
       ==> ~((&0:int) = FST p) /\
           (&0:int) <= SND p /\
           SND p + n <= m (FST p) in
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
   let is_uint32 =
     \z:int. (&0:int) <= z /\ z < (&4294967296:int) in
   let is_sint32 =
     \z:int. --(&2147483648:int) <= z /\ z < (&2147483648:int) in
   let p_unchanged =
     \(m0:(int#int)->int) (m1:(int#int)->int)
      (p:int#int) (lo:int) (hi:int).
       !j:int.
         lo <= j
         ==> j < hi
         ==> m1 (shift p j) = m0 (shift p j) in
   let p_accumulatebounds =
     \(l_accumulate:
         ((int#int)->int)->(int#int)->int->int->int)
      (mem:(int#int)->int) (p:int#int) (n:int) (init:int).
       !j:int.
         let y = l_accumulate mem p j init in
         j <= n
         ==> (&0:int) <= j
         ==> --(&2147483648:int) <= y /\
             y <= (&2147483647:int) in
   let p_partialsum =
     \(l_accumulate:
         ((int#int)->int)->(int#int)->int->int->int)
      (mem:(int#int)->int) (source:int#int)
      (n:int) (destination:int#int).
       !j:int.
         (&0:int) <= j
         ==> j < n
         ==> mem (shift destination j) =
             l_accumulate mem source ((&1:int) + j) (&0:int) in
   !region:int->int.
   !linked:(int->int)->bool.
   !to_uint32 to_sint32:int->int.
   !l_accumulate:
      ((int#int)->int)->(int#int)->int->int->int.
   !a a_1:int#int.
   !t_2 t_1:(int#int)->int.
   !i i_1:int.
   !t:int->int.
     ((!z:int. is_uint32 (to_uint32 z)) /\
      (!z:int. is_uint32 z ==> to_uint32 z = z) /\
      (!z:int. to_uint32 (to_uint32 z) = to_uint32 z) /\
      (!z:int. is_sint32 (to_sint32 z)) /\
      (!z:int. is_sint32 z ==> to_sint32 z = z) /\
      (!z:int. to_sint32 (to_sint32 z) = to_sint32 z) /\
      (!z:int. to_sint32 (to_uint32 z) = to_sint32 z) /\
      (!mem:(int#int)->int.
       !p:int#int.
       !n init:int.
         is_sint32 (l_accumulate mem p n init)) /\
      (!n init:int.
       !mem:(int#int)->int.
       !p:int#int.
         n <= (&0:int)
         ==> is_sint32 init
         ==> l_accumulate mem p n init = init) /\
      (!n init:int.
       !mem:(int#int)->int.
       !p:int#int.
         (&0:int) < n
         ==> is_sint32 init
         ==> mem (shift p (n - (&1:int))) +
             l_accumulate mem p (n - (&1:int)) init =
             l_accumulate mem p n init) /\
      (!init:int.
       !m0 m1:(int#int)->int.
       !p:int#int.
       !n:int.
         is_sint32 init
         ==> p_unchanged m0 m1 p (&0:int) n
         ==> l_accumulate m1 p n init =
             l_accumulate m0 p n init))
     ==>
     let a_2 = shift a (&0:int) in
     let a_3 = shift a_1 (&0:int) in
     let x = t_2 a_3 in
     let a_4 =
       havoc t_1 (update t_2 a_2 x)
         (shift a (&1:int)) (i - (&1:int)) in
     let x_1 = i_1 - (&1:int) in
     let a_5 = a_4 (shift a x_1) in
     let a_6 = a_4 (shift a_1 i_1) in
     let a_7 = a_4 (shift a (to_uint32 x_1)) in
       a_5 = l_accumulate a_4 a_1 i_1 (&0:int)
       ==> (&0:int) < i
       ==> (&0:int) < i_1
       ==> i_1 <= i
       ==> i_1 < i
       ==> region (FST a) <= (&0:int)
       ==> region (FST a_1) <= (&0:int)
       ==> linked t
       ==> is_uint32 i
       ==> is_uint32 i_1
       ==> is_sint32 x
       ==> valid_rd t a_3 (&1:int)
       ==> valid_rd t a_3 i
       ==> valid_rw t a_2 (&1:int)
       ==> valid_rw t a_2 i
       ==> p_accumulatebounds
             l_accumulate t_2 a_1 ((&1:int) + i) (&0:int)
       ==> separated a_3 i a_2 i
       ==> is_sint32 a_6
       ==> is_sint32 a_5
       ==> is_sint32 a_7
       ==> p_unchanged a_4 t_2 a_1 (&0:int) i
       ==> p_partialsum l_accumulate a_4 a_1 i_1 a
       ==> a_6 + a_7 <= (&2147483647:int)`;;
