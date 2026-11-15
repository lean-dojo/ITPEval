(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2:
  a heap-maximum loop-invariant preservation condition asserting that the
  value at the selected nonnegative index is at most the first array value,
  under the stated index, unsigned-integer, heap, prefix-bound, and memory
  region assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !t:(int#int)->int.
   !a:int#int.
   !i i_1 i_2:int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let p_isheap =
       \(mint:(int#int)->int) (base_addr:int#int) (upper:int).
         !j:int.
           (&0:int) < j
           ==> j < upper
           ==> mint (shift base_addr j) <=
               mint
                 (shift base_addr
                   (cdiv (j - (&1:int)) (&2:int))) in
     let x = t (shift a (&0:int)) in
     (&0:int) < i
     ==> i_1 <= i
     ==> (&0:int) <= i_1
     ==> i_1 < i
     ==> i_2 <= i_1
     ==> (&0:int) <= i_2
     ==> region (FST a) <= (&0:int)
     ==> i_1 <= (&4294967294:int)
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> p_isheap t a i
     ==> is_uint32 ((&1:int) + i_1)
     ==> (!i_3:int.
            (&0:int) <= i_3
            ==> i_3 < i_1
            ==> t (shift a i_3) <= x)
     ==> t (shift a i_2) <= x`;;
