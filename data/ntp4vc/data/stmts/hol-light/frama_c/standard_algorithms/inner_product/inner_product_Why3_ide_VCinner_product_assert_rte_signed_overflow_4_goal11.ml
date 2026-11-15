(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_4_goal11:
  the signed 32-bit upper-overflow verification condition for one inner-product
  accumulation step. This file contains no proof.
*)

let statement =
  `let shift =
     \(p:int#int) (k:int). (FST p,SND p + k) in
   let is_uint32 =
     \x:int. (&0:int) <= x /\ x < (&4294967296:int) in
   let is_sint32 =
     \x:int. --(&2147483648:int) <= x /\ x < (&2147483648:int) in
   let valid_rd =
     \(m:int->int) (p:int#int) (n:int).
       (&0:int) < n
       ==> ~((&0:int) = FST p) /\
           (&0:int) <= SND p /\
           SND p + n <= m (FST p) in
   let p_unchanged =
     \(m0:(int#int)->int) (m1:(int#int)->int)
      (p:int#int) (lo:int) (hi:int).
       !j:int.
         lo <= j
         ==> j < hi
         ==> m1 (shift p j) = m0 (shift p j) in
   let p_productbounds =
     \(mem:(int#int)->int) (a:int#int) (b:int#int) (n:int).
       !j:int.
         (&0:int) <= j
         ==> j < n
         ==> --(&2147483648:int) <=
             mem (shift a j) * mem (shift b j) /\
             mem (shift a j) * mem (shift b j) <=
             (&2147483647:int) in
   let p_innerproductbounds =
     \(l_innerproduct:
         ((int#int)->int)->(int#int)->(int#int)->int->int->int)
      (mem:(int#int)->int) (a:int#int) (b:int#int)
      (n:int) (init:int).
       !j:int.
         j <= n
         ==> (&0:int) <= j
         ==> --(&2147483648:int) <=
             l_innerproduct mem a b j init /\
             l_innerproduct mem a b j init <=
             (&2147483647:int) in
   !region:int->int.
   !linked:(int->int)->bool.
   !to_uint32 to_sint32:int->int.
   !l_innerproduct:
      ((int#int)->int)->(int#int)->(int#int)->int->int->int.
   !t_1:(int#int)->int.
   !a:int#int.
   !i_2:int.
   !a_1:int#int.
   !i_1 i:int.
   !t:int->int.
     ((!z:int. is_uint32 (to_uint32 z)) /\
      (!z:int. is_uint32 z ==> to_uint32 z = z) /\
      (!z:int. to_uint32 (to_uint32 z) = to_uint32 z) /\
      (!z:int. is_sint32 (to_sint32 z)) /\
      (!z:int. is_sint32 z ==> to_sint32 z = z) /\
      (!z:int. to_sint32 (to_sint32 z) = to_sint32 z) /\
      (!z:int. to_sint32 (to_uint32 z) = to_sint32 z) /\
      (!n init:int.
       !mem:(int#int)->int.
       !p q:int#int.
         n <= (&0:int)
         ==> is_sint32 init
         ==> l_innerproduct mem p q n init = init) /\
      (!n init:int.
       !mem:(int#int)->int.
       !p q:int#int.
         (&0:int) < n
         ==> is_sint32 init
         ==> l_innerproduct mem p q (n - (&1:int)) init +
             mem (shift p (n - (&1:int))) *
             mem (shift q (n - (&1:int))) =
             l_innerproduct mem p q n init) /\
      (!init:int.
       !m0 m1:(int#int)->int.
       !p q:int#int.
       !n:int.
         is_sint32 init
         ==> p_unchanged m0 m1 p (&0:int) n
         ==> p_unchanged m0 m1 q (&0:int) n
         ==> l_innerproduct m1 p q n init =
             l_innerproduct m0 p q n init))
     ==>
     let x = t_1 (shift a i_2) in
     let x_1 = t_1 (shift a_1 i_2) in
     let x_2 = l_innerproduct t_1 a_1 a i_2 i_1 in
       i_2 <= i
       ==> (&0:int) <= i_2
       ==> i_2 < i
       ==> region (FST a) <= (&0:int)
       ==> region (FST a_1) <= (&0:int)
       ==> linked t
       ==> is_uint32 i
       ==> is_uint32 i_2
       ==> is_sint32 i_1
       ==> p_productbounds t_1 a_1 a i
       ==> is_sint32 x
       ==> is_sint32 x_1
       ==> p_innerproductbounds
             l_innerproduct t_1 a_1 a i i_1
       ==> valid_rd t (shift a (&0:int)) i
       ==> valid_rd t (shift a_1 (&0:int)) i
       ==> is_sint32 x_2
       ==> x_2 + to_sint32 (x * x_1) <=
           (&2147483647:int)`;;
