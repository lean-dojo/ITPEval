(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_loop_inv_2_preserved_goal4:
  a Contiki memb-allocation verification condition stating that the loop
  invariant preserves nonzero allocation markers through the current scan
  index, under the given memory, framing, and integer-range assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a:int#int.
   !t_3:(int#int)->(int#int).
   !i:int.
   !t_2 t_1:(int#int)->int.
   !i_1:int.
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
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
     let is_sint8 =
       \z:int.
         --(&128:int) <= z /\ z < (&128:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let p_valid_memb =
       \(malloc:int->int)
        (mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (m:int#int).
         let elem_size = mint (shift m (&0:int)) in
         let count = mint (shift m (&1:int)) in
         let total_size = count * elem_size in
         let used = mptr (shift m (&2:int)) in
         let memory = mptr (shift m (&3:int)) in
         let used_start = shift used (&0:int) in
         let memory_start = shift memory (&0:int) in
         (&0:int) < elem_size /\
         total_size <= (&2147483647:int) /\
         valid_rw malloc m (&4:int) /\
         valid_rw malloc used (&1:int) /\
         valid_rw malloc memory (&1:int) /\
         valid_rw malloc used_start count /\
         valid_rw malloc memory_start total_size /\
         separated used_start count memory_start total_size in
     let a_1 = shift a (&2:int) in
     let a_2 = t_3 a_1 in
     let a_3 = shift a_2 i in
     let x = t_2 a_3 in
     let a_4 = shift a (&1:int) in
     let x_1 = t_1 a_4 in
     ~(x = (&0:int))
     ==> (&0:int) <= i
     ==> i_1 <= i
     ==> (&0:int) <= i_1
     ==> i < x_1
     ==> i <= x_1
     ==> region (FST a) <= (&0:int)
     ==> i <= (&2147483646:int)
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_uint16 x_1
     ==> is_sint32 ((&1:int) + i)
     ==> p_valid_memb t t_3 t_1 a
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> is_sint8 x
     ==> valid_rd t a_3 (&1:int)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < i
            ==> ~(t_2 (shift a_2 i_2) = (&0:int)))
     ==> ~(t_2 (shift a_2 i_1) = (&0:int))`;;
