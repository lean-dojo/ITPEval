(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_vmult/float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0:
  three sequential memory updates compute the real three-vector obtained by
  multiplying a 3-by-3 floating-point matrix by a vector.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a_2 a:int#int.
   !t_1:(int#int)->real.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let update =
       \(f:(int#int)->real) (p:int#int) (x:real) (q:int#int).
         if q = p then x else f q in
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
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let finite32 = \x:real. T in
     let is_float32 = \x:real. T in
     let finite_floatvect3 =
       \(mem:(int#int)->real) (v:int#int).
         finite32 (mem (shift v (&0:int))) /\
         finite32 (mem (shift v (&1:int))) /\
         finite32 (mem (shift v (&2:int))) in
     let rvalid_floatvect3 =
       \(malloc:int->int) (mem:(int#int)->real) (v:int#int).
         finite_floatvect3 mem v /\
         valid_rd malloc v (&3:int) in
     let finite_floatrmat =
       \(mem:(int#int)->real) (rm:int#int).
         let b = shift rm (&0:int) in
         finite32 (mem (shift b (&0:int))) /\
         finite32 (mem (shift b (&1:int))) /\
         finite32 (mem (shift b (&2:int))) /\
         finite32 (mem (shift b (&3:int))) /\
         finite32 (mem (shift b (&4:int))) /\
         finite32 (mem (shift b (&5:int))) /\
         finite32 (mem (shift b (&6:int))) /\
         finite32 (mem (shift b (&7:int))) /\
         finite32 (mem (shift b (&8:int))) in
     let rvalid_floatrmat =
       \(malloc:int->int) (mem:(int#int)->real) (rm:int#int).
         finite_floatrmat mem rm /\
         valid_rd malloc rm (&9:int) in
     let vector_of_memory =
       \(mem:(int#int)->real) (v:int#int).
         (mem (shift v (&0:int)),
          (mem (shift v (&1:int)),
           mem (shift v (&2:int)))) in
     let matrix_vector =
       \(mem:(int#int)->real) (rm:int#int)
        (v:real#(real#real)).
         let b = shift rm (&0:int) in
         let x = FST v in
         let y = FST (SND v) in
         let z = SND (SND v) in
         (mem (shift b (&0:int)) * x +
          mem (shift b (&1:int)) * y +
          mem (shift b (&2:int)) * z,
          (mem (shift b (&3:int)) * x +
           mem (shift b (&4:int)) * y +
           mem (shift b (&5:int)) * z,
           mem (shift b (&6:int)) * x +
           mem (shift b (&7:int)) * y +
           mem (shift b (&8:int)) * z)) in
     let a_3 = shift a_1 (&0:int) in
     let r = t_1 a_3 in
     let a_4 = shift a_1 (&1:int) in
     let r_1 = t_1 a_4 in
     let a_5 = shift a_1 (&2:int) in
     let r_2 = t_1 a_5 in
     let a_6 = shift a_2 (&0:int) in
     let r_3 = t_1 (shift a_6 (&0:int)) in
     let r_4 = t_1 (shift a_6 (&1:int)) in
     let r_5 = t_1 (shift a_6 (&2:int)) in
     let m =
       update t_1 (shift a (&0:int))
         (r_3 * r + r_4 * r_1 + r_5 * r_2) in
     let r_6 = m a_3 in
     let r_7 = m a_4 in
     let r_8 = m a_5 in
     let r_9 = m (shift a_6 (&3:int)) in
     let r_10 = m (shift a_6 (&4:int)) in
     let r_11 = m (shift a_6 (&5:int)) in
     let m_1 =
       update m (shift a (&1:int))
         (r_9 * r_6 + r_10 * r_7 + r_11 * r_8) in
     let r_12 = m_1 a_3 in
     let r_13 = m_1 a_4 in
     let r_14 = m_1 a_5 in
     let r_15 = m_1 (shift a_6 (&6:int)) in
     let r_16 = m_1 (shift a_6 (&7:int)) in
     let r_17 = m_1 (shift a_6 (&8:int)) in
     let m_2 =
       update m_1 (shift a (&2:int))
         (r_15 * r_12 + r_16 * r_13 + r_17 * r_14) in
     region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> linked t
     ==> valid_rw t a (&3:int)
     ==> rvalid_floatvect3 t t_1 a_1
     ==> rvalid_floatrmat t t_1 a_2
     ==> separated a (&3:int) a_1 (&3:int)
     ==> separated a (&3:int) a_2 (&9:int)
     ==> separated a_1 (&3:int) a_2 (&9:int)
     ==> is_float32 r
     ==> is_float32 r_1
     ==> is_float32 r_2
     ==> is_float32 r_3
     ==> is_float32 r_4
     ==> is_float32 r_5
     ==> is_float32 r_6
     ==> is_float32 r_7
     ==> is_float32 r_8
     ==> is_float32 r_9
     ==> is_float32 r_10
     ==> is_float32 r_11
     ==> is_float32 r_12
     ==> is_float32 r_13
     ==> is_float32 r_14
     ==> is_float32 r_15
     ==> is_float32 r_16
     ==> is_float32 r_17
     ==> vector_of_memory m_2 a =
         matrix_vector m_2 a_2
           (vector_of_memory m_2 a_1)`;;
