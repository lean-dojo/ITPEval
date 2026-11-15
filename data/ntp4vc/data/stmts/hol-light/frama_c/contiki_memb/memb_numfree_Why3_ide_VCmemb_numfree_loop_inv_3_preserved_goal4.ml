(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_preserved_goal4:
  a Contiki memb free-slot-count verification condition stating that the
  occurrence count after processing the current slot equals the updated loop
  count, under the given memory, framing, integer-range, and loop-invariant
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a:int#int.
   !t_1:(int#int)->int.
   !t_3:(int#int)->(int#int).
   !t_2:(int#int)->int.
   !i_2:int.
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
     let l_occ_a =
       \(mchar:(int#int)->int) (e:int) (p:int#int)
        (from_index:int) (to_index:int).
         (&(CARD
              {j:int |
                 from_index <= j /\
                 j < to_index /\
                 mchar (shift p j) = e}):int) in
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
     let a_1 = shift a (&1:int) in
     let x = t_1 a_1 in
     let a_2 = shift a (&2:int) in
     let a_3 = t_3 a_2 in
     let x_1 = l_occ_a t_2 (&0:int) a_3 (&0:int) i_2 in
     let x_2 = (&1:int) + i_2 in
     let a_4 = shift a_3 i_2 in
     let x_3 = t_2 a_4 in
     (&0:int) <= i_2
     ==> i_2 < x
     ==> i_2 <= x
     ==> region (FST a) <= (&0:int)
     ==> x_1 <= i_2
     ==> i_2 <= (&2147483646:int)
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> is_uint16 x
     ==> is_sint32 x_2
     ==> p_valid_memb t t_3 t_1 a
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_1 (&1:int)
     ==> is_sint8 x_3
     ==> valid_rd t a_4 (&1:int)
     ==> is_sint32 x_1
     ==> (if x_3 = (&0:int)
          then (&1:int) + i = i_1 /\
               x_1 = i /\
               i <= (&2147483646:int)
          else x_1 = i_1)
     ==> l_occ_a t_2 (&0:int) a_3 (&0:int) x_2 = i_1`;;
