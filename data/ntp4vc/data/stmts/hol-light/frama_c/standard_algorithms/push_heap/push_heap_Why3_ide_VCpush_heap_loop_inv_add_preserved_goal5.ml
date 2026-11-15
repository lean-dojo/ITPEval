(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_add_preserved_goal5:
  a push-heap loop-invariant preservation condition asserting the specified
  one-element multiset-count addition after a conditional child update, under
  the stated heap, integer-range, memory-validity, linkage, ordering, update,
  and multiset-count assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !i:int.
   !a:int#int.
   !t_2 t_1:(int#int)->int.
   !i_1:int.
   !t_3:(int#int)->int.
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
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m_1:int).
         n <= (&0:int) \/
         m_1 <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m_1 <= SND p \/
         SND p + n <= SND q in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let update =
       \(f:(int#int)->int) (p:int#int) (value:int) (q:int#int).
         if q = p then value else f q in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let l_heapparent =
       \j:int. cdiv (j - (&1:int)) (&2:int) in
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
               mint (shift base_addr (l_heapparent j)) in
     let p_multisetadd =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (upper:int) (value:int).
         (&1:int) +
           l_count mint1 base_addr (&0:int) upper value =
         l_count mint0 base_addr (&0:int) upper value in
     let p_multisetminus =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (upper:int) (value:int).
         (&1:int) +
           l_count mint0 base_addr (&0:int) upper value =
         l_count mint1 base_addr (&0:int) upper value in
     let p_multisetretain =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (upper:int) (value:int).
         l_count mint1 base_addr (&0:int) upper value =
         l_count mint0 base_addr (&0:int) upper value in
     let p_multisetretainrest =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (upper:int) (v:int) (w:int).
         !value:int.
           ~(value = v)
           ==> ~(value = w)
           ==> is_sint32 value
           ==> p_multisetretain
                 mint0 mint1 base_addr upper value in
     let x = i - (&1:int) in
     let x_1 = l_heapparent x in
     let a_1 = shift a x_1 in
     let x_2 = t_2 a_1 in
     let a_2 = shift a x in
     let x_3 = t_2 a_2 in
     let m = update t_2 a_2 x_2 in
     let a_3 = shift a (&0:int) in
     let a_4 = havoc t_1 m a_3 i in
     let a_5 = shift a i_1 in
     let a_6 = a_4 a_5 in
     let x_4 = l_heapparent i_1 in
     let a_7 = shift a x_4 in
     let a_8 = a_4 a_7 in
     let x_5 = t_3 a_7 in
     let a_9 = shift a (to_uint32 x) in
     (!n m_1 value:int.
        !mint:(int#int)->int.
        !base_addr:int#int.
          n <= m_1
          ==> is_sint32 value
          ==> l_count mint base_addr m_1 n value = (&0:int))
     ==> (!n value m_1:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              mint (shift base_addr (n - (&1:int))) = value
              ==> m_1 < n
              ==> is_sint32 value
              ==> (&1:int) +
                  l_count mint base_addr m_1 (n - (&1:int)) value =
                  l_count mint base_addr m_1 n value)
     ==> (!n value m_1:int.
            !mint:(int#int)->int.
            !base_addr:int#int.
              ~(mint (shift base_addr (n - (&1:int))) = value)
              ==> m_1 < n
              ==> is_sint32 value
              ==> l_count mint base_addr m_1 (n - (&1:int)) value =
                  l_count mint base_addr m_1 n value)
     ==> (!value m_1 n:int.
            !mint0 mint1:(int#int)->int.
            !base_addr:int#int.
              is_sint32 value
              ==> p_unchanged mint0 mint1 base_addr m_1 n
              ==> l_count mint1 base_addr m_1 n value =
                  l_count mint0 base_addr m_1 n value)
     ==> (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> (&0:int) < i
     ==> (&0:int) < i_1
     ==> (&0:int) <= i_1
     ==> region (FST a) <= (&0:int)
     ==> (&0:int) < x_1
     ==> x_2 < x_3
     ==> a_6 < x_3
     ==> a_8 < x_3
     ==> (&2:int) <= i
     ==> (&2:int) + i_1 <= i
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 x_4
     ==> valid_rd t a_5 (&1:int)
     ==> valid_rw t a_3 i
     ==> is_uint32 x_1
     ==> p_isheap t_2 a x
     ==> is_sint32 x_5
     ==> valid_rd t a_7 (&1:int)
     ==> is_uint32 (l_heapparent x_1)
     ==> is_sint32 x_3
     ==> is_sint32 x_2
     ==> valid_rd t a_9 (&1:int)
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rw t a_9 (&1:int)
     ==> is_sint32 (m a_1)
     ==> is_sint32 a_6
     ==> is_sint32 a_8
     ==> p_isheap a_4 a i
     ==> p_multisetminus a_4 t_2 a i x_3
     ==> p_multisetadd a_4 t_2 a i a_6
     ==> p_multisetretainrest a_4 t_2 a i x_3 a_6
     ==> (if a_6 < a_8
          then
            update a_4 a_5 a_8 = t_3 /\
            valid_rw t a_5 (&1:int)
          else a_4 = t_3)
     ==> p_multisetadd t_3 t_2 a i x_5`;;
