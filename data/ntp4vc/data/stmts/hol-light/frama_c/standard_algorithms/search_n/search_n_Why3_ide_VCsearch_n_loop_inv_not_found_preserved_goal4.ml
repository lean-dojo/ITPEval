(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_loop_inv_not_found_preserved_goal4:
  a search_n loop-invariant preservation condition concluding that the prefix
  bounded by the incremented search position contains no constant subrange of
  the requested length and value, under the stated C integer ranges, memory
  validity, constant-range, no-prior-subrange, and branch-state assumptions.
  This file contains no proof.
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
   !i_4:int.
   !a:int#int.
   !t_1:(int#int)->int.
   !i i_2 i_3:int.
   !t:int->int.
   !i_1 i_5:int.
     let x = (&1:int) + i_4 in
     let a_1 = shift a i_4 in
     let x_1 = t_1 a_1 in
     let x_2 = t_1 (shift a (i - (&1:int))) in
     (&0:int) < i_2
     ==> i_2 <= i_3
     ==> i_4 < i_3
     ==> region (FST a) <= (&0:int)
     ==> i_4 <= (&4294967294:int)
     ==> i <= x
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_sint32 i_5
     ==> is_uint32 x
     ==> is_sint32 x_1
     ==> p_constantrange t_1 a i i_4 i_5
     ==> ~p_hasconstantsubrange t_1 a i_4 i_2 i_5
     ==> valid_rd t (shift a (&0:int)) i_3
     ==> valid_rd t a_1 (&1:int)
     ==> is_sint32 x_2
     ==> ((&0:int) < i ==> ~(x_2 = i_5))
     ==> (~(x_1 = i_5) \/
          (i_1 = i /\
           ~(i_1 + i_2 = x) /\
           i_1 <= x /\
           i_4 <= (&4294967294:int) + i_1))
     ==> ~p_hasconstantsubrange t_1 a x i_2 i_5`;;
