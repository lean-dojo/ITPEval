(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9:
  a pop-heap loop-invariant establishment condition asserting that the root
  value is an upper bound for the heap prefix, under the stated index,
  memory-validity, integer-range, heap, maximum-child, linkage, and memory-
  region assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !i:int.
   !t_1:(int#int)->int.
   !a:int#int.
   !i_1:int.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
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
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let l_heapparent =
       \j:int. cdiv (j - (&1:int)) (&2:int) in
     let p_isheap =
       \(mint:(int#int)->int) (base_addr:int#int) (upper:int).
         !j:int.
           (&0:int) < j
           ==> j < upper
           ==> mint (shift base_addr j) <=
               mint (shift base_addr (l_heapparent j)) in
     let p_upperbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let p_heapmaximumchild =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (parent:int) (child:int).
         let left = (&1:int) + (&2:int) * parent in
         let child_value = mint (shift base_addr child) in
         let right = (&2:int) + (&2:int) * parent in
         (&0:int) <= parent /\
         (&2:int) + parent <= upper /\
         (parent <= (&2147483646:int)
          ==> l_heapparent child = parent) /\
         ((&2:int) + left <= upper
          ==> mint (shift base_addr left) <= child_value) /\
         ((&2:int) + right <= upper
          ==> mint (shift base_addr right) <= child_value) in
     let x = i - (&1:int) in
     let x_1 = t_1 (shift a x) in
     let a_1 = shift a (&0:int) in
     let x_2 = t_1 a_1 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (&0:int) < i
     ==> (&0:int) < i_1
     ==> region (FST a) <= (&0:int)
     ==> x_1 < x_2
     ==> (&2:int) <= i
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> p_isheap t_1 a i
     ==> is_sint32 x_2
     ==> p_heapmaximumchild t_1 a i (&0:int) i_1
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rw t a_1 i
     ==> is_sint32
           (t_1 (shift a (l_heapparent (&0:int))))
     ==> is_sint32 x_1
     ==> valid_rd t (shift a (to_uint32 x)) (&1:int)
     ==> ((&2:int) + i_1 <= i
          ==> l_heapparent i_1 = (&0:int))
     ==> p_upperbound t_1 a (&0:int) i x_2`;;
