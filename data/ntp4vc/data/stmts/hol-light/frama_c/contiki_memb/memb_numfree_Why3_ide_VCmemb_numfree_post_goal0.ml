(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_post_goal0:
  a Contiki memb free-slot-count verification condition stating that the
  occurrence count through the loaded member count equals the memb pool's
  number of free slots, under the given memory, framing, linkage, and
  integer-range assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a:int#int.
   !t_1:(int#int)->int.
   !t_3:(int#int)->(int#int).
   !t_2:(int#int)->int.
   !i:int.
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
     let l__memb_numfree =
       \(mptr:(int#int)->(int#int))
        (mchar:(int#int)->int)
        (mint:(int#int)->int)
        (m:int#int).
         l_occ_a mchar (&0:int) (mptr (shift m (&2:int)))
           (&0:int) (mint (shift m (&1:int))) in
     let a_1 = shift a (&1:int) in
     let x = t_1 a_1 in
     let a_2 = t_3 (shift a (&2:int)) in
     let x_1 = l_occ_a t_2 (&0:int) a_2 (&0:int) i in
     (&0:int) <= i
     ==> x <= i
     ==> i <= x
     ==> region (FST a) <= (&0:int)
     ==> x_1 <= i
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_sint32 i
     ==> is_uint16 x
     ==> p_valid_memb t t_3 t_1 a
     ==> valid_rd t a_1 (&1:int)
     ==> is_sint32 x_1
     ==> l_occ_a t_2 (&0:int) a_2 (&0:int) x =
         l__memb_numfree t_3 t_2 t_1 a`;;
