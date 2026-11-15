(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_minus_established_goal15:
  a push-heap loop-invariant establishment condition asserting the specified
  one-element multiset-count removal of the former child value after replacing
  the final child position with its parent value, under the stated heap,
  integer-range, memory-validity, linkage, and ordering assumptions. This file
  contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !i:int.
   !a:int#int.
   !t_1:(int#int)->int.
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
     let p_unchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint1 (shift base_addr j) =
               mint0 (shift base_addr j) in
     let p_multisetminus =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (upper:int) (value:int).
         (&1:int) +
           l_count mint0 base_addr (&0:int) upper value =
         l_count mint1 base_addr (&0:int) upper value in
     let update =
       \(f:(int#int)->int) (p:int#int) (value:int) (q:int#int).
         if q = p then value else f q in
     let x = i - (&1:int) in
     let x_1 = l_heapparent x in
     let a_1 = shift a x_1 in
     let x_2 = t_1 a_1 in
     let a_2 = shift a x in
     let x_3 = t_1 a_2 in
     let a_3 = shift a (to_uint32 x) in
     let m = update t_1 a_2 x_2 in
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
     ==> region (FST a) <= (&0:int)
     ==> (&0:int) < x_1
     ==> x_2 < x_3
     ==> (&2:int) <= i
     ==> linked t
     ==> is_uint32 i
     ==> valid_rw t (shift a (&0:int)) i
     ==> is_uint32 x_1
     ==> p_isheap t_1 a x
     ==> is_uint32 (l_heapparent x_1)
     ==> is_sint32 x_3
     ==> is_sint32 x_2
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rw t a_3 (&1:int)
     ==> is_sint32 (m a_1)
     ==> p_multisetminus m t_1 a i x_3`;;
