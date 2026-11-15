(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/max_element/max_element_Why3_ide_VCmax_element_post_result_goal2:
  a max-element postcondition verification condition asserting that a
  nonpositive unsigned 32-bit integer is nonnegative, under the stated memory
  region, linkage, and valid-read assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !i:int.
   !a:int#int.
   !t:int->int.
     let shift =
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
     i <= (&0:int)
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> valid_rd t (shift a (&0:int)) i
     ==> (&0:int) <= i`;;
