(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/standard_algorithms/remove_copy/remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5:
  a remove-copy loop-invariant preservation condition asserting that the
  retained output prefix has the same multiplicities as the processed input
  prefix for every signed 32-bit value other than the removed value, after the
  conditional copy step and under the stated count, range, memory-validity,
  separation, linkage, and unchanged-memory assumptions. This file contains
  no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !l_count:
      ((int#int)->int)->(int#int)->int->int->int->int.
   !t_3:(int#int)->int.
   !a_1:int#int.
   !i_5 i:int.
   !a:int#int.
   !t_1:(int#int)->int.
   !i_2:int.
   !t:int->int.
   !i_1 i_3 i_4:int.
   !t_2:(int#int)->int.
   !p:bool.
     let shift =
       \(q:int#int) (k:int). (FST q,SND q + k) in
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
       \(f:(int#int)->int) (q:int#int) (value:int) (r:int#int).
         if r = q then value else f r in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let p_hasvalue =
       \(mint:(int#int)->int) (base_addr:int#int)
        (lower:int) (upper:int) (value:int).
         ?j:int.
           mint (shift base_addr j) = value /\
           lower <= j /\
           j < upper in
     let p_unchanged =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (base_addr:int#int) (lower:int) (upper:int).
         !j:int.
           lower <= j
           ==> j < upper
           ==> mint1 (shift base_addr j) =
               mint0 (shift base_addr j) in
     let p_multisetretainrest =
       \(mint0:(int#int)->int) (mint1:(int#int)->int)
        (input_addr:int#int) (input_lower:int) (input_upper:int)
        (output_addr:int#int) (output_lower:int) (output_upper:int)
        (removed:int).
         !value:int.
           ~(value = removed)
           ==> is_sint32 value
           ==> l_count mint1 input_addr input_lower input_upper value =
               l_count mint0 output_addr output_lower output_upper value in
     let x = l_count t_3 a_1 (&0:int) i_5 i in
     let x_1 = (&1:int) + i_5 in
     let a_2 = shift a_1 (&0:int) in
     let a_3 = shift a_1 i_5 in
     let a_4 = shift a (&0:int) in
     let x_2 = i_5 - x in
     let a_5 = havoc t_1 t_3 a_4 i_2 in
     let a_6 = a_5 a_3 in
     let a_7 = shift a x_2 in
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
     ==> i_5 <= i_2
     ==> i_5 < i_2
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> x <= i_5
     ==> (&0:int) <= x
     ==> i_5 <= (&4294967294:int)
     ==> linked t
     ==> is_uint32 i_1
     ==> is_uint32 i_2
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> is_uint32 i_5
     ==> is_sint32 i
     ==> is_uint32 x_1
     ==> valid_rd t a_2 i_2
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rw t a_4 i_2
     ==> separated a_2 i_2 a (&1:int)
     ==> is_uint32 x_2
     ==> is_sint32 a_6
     ==> ~p_hasvalue a_5 a (&0:int) x_2 i
     ==> p_unchanged a_5 t_3 a_1 i_5 i_2
     ==> p_unchanged a_5 t_3 a x_2 i_2
     ==> p_multisetretainrest
           a_5 t_3 a_1 (&0:int) i_5 a (&0:int) x_2 i
     ==> (if a_6 = i
          then
            a_5 = t_2 /\
            i_4 + l_count t_3 a_1 (&0:int) i_5 (t_2 a_3) = i_5
          else
            p = F /\
            i_3 = i_1 /\
            i_1 + x = i_5 /\
            i_3 + x = i_5 /\
            i_4 + x = x_1 /\
            update a_5 a_7 a_6 = t_2 /\
            i_5 <= (&4294967294:int) + x /\
            valid_rw t a_7 (&1:int))
     ==> p_multisetretainrest
           t_2 t_3 a_1 (&0:int) x_1 a (&0:int) i_4 i`;;
