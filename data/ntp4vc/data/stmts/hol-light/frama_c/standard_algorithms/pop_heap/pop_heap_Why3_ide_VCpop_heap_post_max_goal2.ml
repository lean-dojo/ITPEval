(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_max_goal2:
  a pop-heap postcondition verification condition asserting that the final
  array prefix has its last index as a maximum element, under the stated heap,
  maximum-child, upper-bound, integer-range, memory-validity, linkage, and
  memory-region assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_4:(int#int)->int.
   !i i_1:int.
   !t_3:(int#int)->int.
   !i_3:int.
   !t:int->int.
   !i_2:int.
   !t_5:(int#int)->int.
   !p p_1:bool.
   !t_1:int->int.
   !t_2:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let valid_rw =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST q /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let valid_rd =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST q) /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let separated =
       \(q:int#int) (n:int) (r:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST q = FST r) \/
         SND r + m <= SND q \/
         SND q + n <= SND r in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (q:int#int) (n:int) (r:int#int).
         if separated r (&1:int) q n then m1 r else m0 r in
     let update =
       \(f:(int#int)->int) (q:int#int) (v:int) (r:int#int).
         if r = q then v else f r in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_unchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint1 (shift base_addr j) =
               mint0 (shift base_addr j) in
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
     let p_maxelement =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (maximum_index:int).
         (&0:int) <= maximum_index /\
         maximum_index < upper /\
         p_upperbound mint base_addr (&0:int) upper
           (mint (shift base_addr maximum_index)) in
     let l_heapleft =
       \j:int. (&1:int) + (&2:int) * j in
     let l_heapright =
       \j:int. (&2:int) + (&2:int) * j in
     let p_heapmaximumchild =
       \(mint:(int#int)->int) (base_addr:int#int)
        (upper:int) (parent:int) (child:int).
         let left = l_heapleft parent in
         let child_value = mint (shift base_addr child) in
         let right = l_heapright parent in
         (&0:int) <= parent /\
         (&2:int) + parent <= upper /\
         (parent <= (&2147483646:int)
          ==> l_heapparent child = parent) /\
         ((&2:int) + left <= upper
          ==> mint (shift base_addr left) <= child_value) /\
         ((&2:int) + right <= upper
          ==> mint (shift base_addr right) <= child_value) in
     let a_1 = shift a (&0:int) in
     let x = t_4 a_1 in
     let x_1 = i - (&1:int) in
     let a_2 = shift a x_1 in
     let a_3 = shift a (to_uint32 x_1) in
     let a_4 = shift a i_1 in
     let x_2 = t_3 a_2 in
     let a_5 = shift a i_3 in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (!n m value:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              n <= m
              ==> is_sint32 value
              ==> l_count mint base_addr m n value = (&0:int))
     ==> (!n value m:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              mint (shift base_addr (n - (&1:int))) = value
              ==> m < n
              ==> is_sint32 value
              ==> (&1:int) +
                  l_count mint base_addr m (n - (&1:int)) value =
                  l_count mint base_addr m n value)
     ==> (!n value m:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              ~(mint (shift base_addr (n - (&1:int))) = value)
              ==> m < n
              ==> is_sint32 value
              ==> l_count mint base_addr m (n - (&1:int)) value =
                  l_count mint base_addr m n value)
     ==> (!value m n:int.
            !mint0 mint1:(int#int)->int.
            !base_addr:int#int.
              is_sint32 value
              ==> p_unchanged mint0 mint1 base_addr m n
              ==> l_count mint1 base_addr m n value =
                  l_count mint0 base_addr m n value)
     ==> (&0:int) < i
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> p_isheap t_4 a i
     ==> is_sint32 x
     ==> valid_rw t a_1 i
     ==> is_sint32 (t_5 a_2)
     ==> (if (&2:int) <= i
          then
            valid_rd t a_1 (&1:int) /\
            valid_rd t a_3 (&1:int) /\
            (if t_4 a_2 < x
             then
               p = F /\
               p_1 = F /\
               t_1 = t /\
               havoc t_2 t_4 a_1 x_1 = t_3 /\
               update (update t_3 a_4 x_2) a_2 x = t_5 /\
               (&0:int) < i_2 /\
               (&0:int) <= i_1 /\
               i_1 < i_3 /\
               x_2 < t_3 (shift a (l_heapparent i_1)) /\
               (&2:int) + i_1 <= i /\
               p_isheap t_3 a i /\
               p_heapmaximumchild t_3 a i i_1 i_3 /\
               p_heapmaximumchild t_4 a i (&0:int) i_2 /\
               valid_rw t_1 a_1 i /\
               valid_rw t_1 a_4 (&1:int) /\
               p_upperbound t_3 a (&0:int) i x /\
               valid_rd t_1 a_3 (&1:int) /\
               valid_rw t_1 a_3 (&1:int) /\
               ((&2:int) + i_2 <= i
                ==> l_heapparent i_2 = (&0:int)) /\
               ((&2:int) + i_3 <= i
                ==> l_heapparent i_3 = i_1) /\
               (i <= (&1:int) + i_3 \/
                t_3 a_5 <= x_2 /\ valid_rd t_1 a_5 (&1:int)) /\
               (!value:int.
                  is_sint32 value
                  ==> l_count t_4 a (&0:int) i value +
                      (if t_3 a_4 = value then (&1:int) else (&0:int)) =
                      l_count t_3 a (&0:int) i value +
                      (if x = value then (&1:int) else (&0:int)))
             else t_5 = t_4)
          else t_5 = t_4)
     ==> p_maxelement t_5 a i x_1`;;
