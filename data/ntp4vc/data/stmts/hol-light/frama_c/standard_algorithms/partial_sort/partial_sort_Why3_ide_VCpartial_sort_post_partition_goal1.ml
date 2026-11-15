(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1:
  a partial-sort postcondition verification condition asserting that the
  resulting array is partitioned at the selected prefix boundary, under the
  stated index, memory-validity, integer-range, sorting, heap, multiset,
  bound, linkage, and memory-region assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_6 t_3 t_5:(int#int)->int.
   !i_2 i_1 i:int.
   !t:int->int.
   !p:bool.
   !t_1:int->int.
   !t_2 t_8 t_4 t_7:(int#int)->int.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
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
     let p_sorted =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int).
         !j k:int.
           k < upper
           ==> lower <= j
           ==> j < k
           ==> mint (shift base_addr j) <=
               mint (shift base_addr k) in
     let p_partition =
       \(mint:(int#int)->int) (base_addr:int#int)
        (middle:int) (upper:int).
         (&0:int) <= middle
         ==> middle <= upper
         ==> (!j k:int.
                middle <= k
                ==> k < upper
                ==> (&0:int) <= j
                ==> j < middle
                ==> mint (shift base_addr j) <=
                    mint (shift base_addr k)) in
     let p_isheap =
       \(mint:(int#int)->int) (base_addr:int#int) (upper:int).
         !j:int.
           (&0:int) < j
           ==> j < upper
           ==> mint (shift base_addr j) <=
               mint
                 (shift base_addr
                   (cdiv (j - (&1:int)) (&2:int))) in
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let p_upperbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint (shift base_addr j) <= value in
     let p_lowerbound =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> value <= mint (shift base_addr j) in
     let a_1 = shift a (&0:int) in
     let x = t_6 a_1 in
     let a_2 = havoc t_3 t_5 a_1 i_2 in
     (!n m value:int.
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
     ==> i_1 <= i
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_sint32 (t_5 a_1)
     ==> is_sint32 x
     ==> valid_rw t a_1 i
     ==> (if (&0:int) < i_1
          then p = F /\
               t_1 = t /\
               havoc t_2 t_8 a_1 i_1 = t_5 /\
               havoc t_3 t_5 a_1 i = t_6 /\
               havoc t_4 a_2 a_1 i_1 = t_7 /\
               i_2 <= i /\
               i <= i_2 /\
               i_1 <= i_2 /\
               p_sorted t_7 a (&0:int) i_1 /\
               p_isheap t_5 a i_1 /\
               p_isheap t_6 a i_1 /\
               p_multisetunchanged t_5 t_8 a (&0:int) i_1 /\
               p_multisetunchanged t_6 t_8 a (&0:int) i_2 /\
               p_unchanged t_6 t_8 a i_2 i /\
               valid_rw t_1 a_1 i_1 /\
               p_upperbound t_6 a (&0:int) i_1 x /\
               p_lowerbound t_6 a i_1 i_2 x /\
               p_multisetunchanged t_7 a_2 a (&0:int) i_1
          else t_8 = t_7)
     ==> p_partition t_7 a i_1 i`;;
