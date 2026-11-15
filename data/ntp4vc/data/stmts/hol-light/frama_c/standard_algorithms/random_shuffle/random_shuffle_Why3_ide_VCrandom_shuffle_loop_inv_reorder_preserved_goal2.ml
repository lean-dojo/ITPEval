(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/random_shuffle/random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_reorder_preserved_goal2:
  a random-shuffle loop verification condition asserting preservation of the
  multiset of signed 32-bit values in the extended array prefix after the
  stated pair of memory updates, under the index, memory-validity, linkage,
  integer-range, unchanged-range, and counting assumptions. This file contains
  no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !a:int#int.
   !t_1 t_2:(int#int)->int.
   !i_2 i_3 i_1 i:int.
   !t:int->int.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
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
     let update =
       \(f:(int#int)->int) (q:int#int) (value:int) (r:int#int).
         if r = q then value else f r in
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
     let p_multisetunchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !value:int.
           is_sint32 value
           ==> l_count mint1 base_addr lower upper value =
               l_count mint0 base_addr lower upper value in
     let a_1 = shift a (&0:int) in
     let a_2 = havoc t_1 t_2 a_1 i_2 in
     let a_3 = shift a i_3 in
     let a_4 = shift a (to_uint32 ((&1:int) + i_1)) in
     let a_5 = a_2 a_3 in
     let a_6 = update (update a_2 a_3 i) a_4 a_5 in
     let a_7 = a_6 a_3 in
     let a_8 = a_2 a_4 in
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
     ==> a_7 = a_8
     ==> (&0:int) < i_2
     ==> (&0:int) < i_3
     ==> (&0:int) <= i_1
     ==> i_1 < i_3
     ==> i_3 <= i_2
     ==> i_3 < i_2
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> valid_rw t a_1 i_2
     ==> valid_rw t a_3 (&1:int)
     ==> is_sint32 a_5
     ==> is_sint32 a_8
     ==> valid_rw t a_4 (&1:int)
     ==> is_sint32 a_7
     ==> p_unchanged a_2 t_2 a i_3 i_2
     ==> p_multisetunchanged a_2 t_2 a (&0:int) i_3
     ==> p_multisetunchanged
           a_6 t_2 a (&0:int) (to_uint32 ((&1:int) + i_3))`;;
