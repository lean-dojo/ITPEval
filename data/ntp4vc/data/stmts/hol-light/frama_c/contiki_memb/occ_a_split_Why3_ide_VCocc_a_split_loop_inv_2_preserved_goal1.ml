(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1:
  a Contiki occurrence-count split verification condition stating that a
  count decomposition remains valid when the upper endpoint is incremented,
  under the given interval, memory-region, constancy, and signed-32-bit
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !sconst:((int#int)->int)->bool.
   !t:(int#int)->int.
   !i_3:int.
   !a:int#int.
   !i_2 i_4 i_1 i:int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let l_occ_a =
       \(mchar:(int#int)->int) (e:int) (p:int#int)
        (from_index:int) (to_index:int).
         (&(CARD
              {j:int |
                 from_index <= j /\
                 j < to_index /\
                 mchar (shift p j) = e}):int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let x = l_occ_a t i_3 a i_2 i_4 in
     let x_1 = (&1:int) + i_1 in
     x + l_occ_a t i_3 a i_4 i_1 =
       l_occ_a t i_3 a i_2 i_1
     ==> i_1 <= i
     ==> i_4 <= i
     ==> i_1 < i
     ==> i_4 <= i_1
     ==> i_2 <= i_4
     ==> region (FST a) <= (&0:int)
     ==> i_1 <= (&2147483646:int)
     ==> sconst t
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> is_sint32 i_3
     ==> is_sint32 i_4
     ==> is_sint32 x_1
     ==> x + l_occ_a t i_3 a i_4 x_1 =
         l_occ_a t i_3 a i_2 x_1`;;
