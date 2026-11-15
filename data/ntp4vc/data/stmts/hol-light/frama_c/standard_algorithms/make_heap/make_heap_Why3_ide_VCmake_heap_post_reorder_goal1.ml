(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_post_reorder_goal1:
  a make-heap postcondition verification condition asserting preservation of
  the array prefix multiset after the reorder, under the stated memory,
  integer-range, heap, unchanged-range, and linkage assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !i_1:int.
   !t:int->int.
   !i:int.
   !p:bool.
   !t_1 t_3 t_2:(int#int)->int.
     let shift =
       \(base_addr:int#int) (k:int).
         (FST base_addr,SND base_addr + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
     let valid_rw =
       \(malloc:int->int) (base_addr:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST base_addr /\
             (&0:int) <= SND base_addr /\
             SND base_addr + n <= malloc (FST base_addr) in
     let separated =
       \(base_addr:int#int) (n:int) (other_addr:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST base_addr = FST other_addr) \/
         SND other_addr + m <= SND base_addr \/
         SND base_addr + n <= SND other_addr in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (base_addr:int#int) (n:int) (q:int#int).
         if separated q (&1:int) base_addr n then m1 q else m0 q in
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
     let a_1 = shift a (&0:int) in
     let x = (&1:int) + i_1 in
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
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> valid_rw t a_1 i
     ==> (if (&0:int) < i
          then p = F /\
               havoc t_1 t_3 a_1 i = t_2 /\
               (&0:int) < i_1 /\
               i_1 <= i /\
               i <= i_1 /\
               p_isheap t_2 a i_1 /\
               p_multisetunchanged
                 t_2 t_3 a (&0:int) x /\
               p_unchanged t_2 t_3 a x i
          else t_3 = t_2)
     ==> p_multisetunchanged
           t_2 t_3 a (&0:int) i`;;
