(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_post_reorder_goal1:
  preservation of all signed-32-bit multiset counts on the push-heap range
  after the stated conditional reorder, under the heap, integer-range,
  memory-validity, linkage, update, havoc, and multiset-count assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !i_1 i_5 i_3 i i_2 i_4:int.
   !t_4 t_2 t_3 t_1:(int#int)->int.
   !t:int->int.
   !p_1 p:bool.
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
     let valid_rd =
       \(malloc:int->int) (q:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST q) /\
             (&0:int) <= SND q /\
             SND q + n <= malloc (FST q) in
     let separated =
       \(q:int#int) (n:int) (r:int#int) (m_1:int).
         n <= (&0:int) \/
         m_1 <= (&0:int) \/
         ~(FST q = FST r) \/
         SND r + m_1 <= SND q \/
         SND q + n <= SND r in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (q:int#int) (n:int) (r:int#int).
         if separated r (&1:int) q n then m1 r else m0 r in
     let update =
       \(f:(int#int)->int) (q:int#int) (value:int) (r:int#int).
         if r = q then value else f r in
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
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let a_1 = shift a (&0:int) in
     let x = i_1 - (&1:int) in
     let a_2 = shift a i_5 in
     let a_3 = shift a (to_uint32 x) in
     let x_1 = t_4 a_2 in
     let a_4 = shift a x in
     let x_2 = t_4 a_4 in
     let a_5 = shift a i_3 in
     let m = update t_4 a_4 x_1 in
     let x_3 = t_2 a_5 in
     let a_6 = shift a i in
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
     ==> (&0:int) < i_1
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_uint32 i_5
     ==> valid_rw t a_1 i_1
     ==> p_isheap t_4 a x
     ==> (if (&2:int) <= i_1
          then
            p_1 = F /\
            l_heapparent x = i_5 /\
            valid_rd t a_2 (&1:int) /\
            valid_rd t a_3 (&1:int) /\
            (if x_1 < x_2
             then
               update t_2 a_5 x_2 = t_3 /\
               valid_rw t a_5 (&1:int) /\
               valid_rw t a_3 (&1:int) /\
               (if (&0:int) < i_5
                then
                  p = F /\
                  i_3 = i_2 /\
                  i_4 = i_2 /\
                  i_4 = i_3 /\
                  l_heapparent i_3 = i /\
                  havoc t_1 m a_1 i_1 = t_2 /\
                  (&0:int) <= i_3 /\
                  x_3 < x_2 /\
                  (&2:int) + i_3 <= i_1 /\
                  p_isheap t_2 a i_1 /\
                  p_multisetadd t_2 t_4 a i_1 x_3 /\
                  p_multisetminus t_2 t_4 a i_1 x_2 /\
                  p_multisetretainrest
                    t_2 t_4 a i_1 x_2 x_3 /\
                  (i_3 <= (&0:int) \/
                   x_2 <= t_2 a_6 /\ valid_rd t a_6 (&1:int))
                else i_5 = i_3 /\ m = t_2)
             else t_4 = t_3)
          else t_4 = t_3)
     ==> p_multisetunchanged t_3 t_4 a (&0:int) i_1`;;
