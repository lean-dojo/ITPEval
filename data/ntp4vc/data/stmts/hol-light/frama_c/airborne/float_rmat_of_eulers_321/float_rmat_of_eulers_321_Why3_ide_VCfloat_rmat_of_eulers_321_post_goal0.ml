(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_of_eulers_321/float_rmat_of_eulers_321_Why3_ide_VCfloat_rmat_of_eulers_321_post_goal0:
  the nine sine-and-cosine entries produced from 3-2-1 Euler angles form a
  real rotation matrix under the source memory and floating-point assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a:int#int.
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
     let finite32 = \x:real. T in
     let is_float32 = \x:real. T in
     let finite_floateulers =
       \(mem:(int#int)->real) (e:int#int).
         finite32 (mem (shift e (&0:int))) /\
         finite32 (mem (shift e (&2:int))) /\
         finite32 (mem (shift e (&1:int))) in
     let rvalid_floateulers =
       \(malloc:int->int) (mem:(int#int)->real) (e:int#int).
         finite_floateulers mem e /\
         valid_rd malloc e (&3:int) in
     let matrix_of_memory =
       \(mem:(int#int)->real) (rm:int#int).
         let b = shift rm (&0:int) in
         ((mem (shift b (&0:int)),
           (mem (shift b (&1:int)),
            mem (shift b (&2:int)))),
          ((mem (shift b (&3:int)),
            (mem (shift b (&4:int)),
             mem (shift b (&5:int)))),
           (mem (shift b (&6:int)),
            (mem (shift b (&7:int)),
             mem (shift b (&8:int)))))) in
     let rotation_matrix =
       \(m:(real#(real#real))#
           ((real#(real#real))#(real#(real#real)))).
         let row0 = FST m in
         let row1 = FST (SND m) in
         let row2 = SND (SND m) in
         let a00 = FST row0 in
         let a01 = FST (SND row0) in
         let a02 = SND (SND row0) in
         let a10 = FST row1 in
         let a11 = FST (SND row1) in
         let a12 = SND (SND row1) in
         let a20 = FST row2 in
         let a21 = FST (SND row2) in
         let a22 = SND (SND row2) in
         a00 * a00 + a01 * a01 + a02 * a02 = (&1:real) /\
         a00 * a10 + a01 * a11 + a02 * a12 = (&0:real) /\
         a00 * a20 + a01 * a21 + a02 * a22 = (&0:real) /\
         a10 * a00 + a11 * a01 + a12 * a02 = (&0:real) /\
         a10 * a10 + a11 * a11 + a12 * a12 = (&1:real) /\
         a10 * a20 + a11 * a21 + a12 * a22 = (&0:real) /\
         a20 * a00 + a21 * a01 + a22 * a02 = (&0:real) /\
         a20 * a10 + a21 * a11 + a22 * a12 = (&0:real) /\
         a20 * a20 + a21 * a21 + a22 * a22 = (&1:real) in
     let r = t_1 (shift a_1 (&0:int)) in
     let r_1 = sin r in
     let r_2 = t_1 (shift a_1 (&2:int)) in
     let r_3 = sin r_2 in
     let r_4 = t_1 (shift a_1 (&1:int)) in
     let r_5 = sin r_4 in
     let r_6 = cos r in
     let r_7 = cos r_2 in
     let r_8 = cos r_4 in
     let a_2 = shift a (&0:int) in
     let r_9 = r_1 * r_5 in
     let r_10 = r_6 * r_5 in
     let m_0 =
       update t_1 (shift a_2 (&0:int))
         (r_8 * r_7) in
     let m_1 =
       update m_0 (shift a_2 (&1:int))
         (r_8 * r_3) in
     let m_2 =
       update m_1 (shift a_2 (&2:int))
         (--r_5) in
     let m_3 =
       update m_2 (shift a_2 (&3:int))
         (r_9 * r_7 + --(r_6 * r_3)) in
     let m_4 =
       update m_3 (shift a_2 (&4:int))
         (r_9 * r_3 + r_6 * r_7) in
     let m_5 =
       update m_4 (shift a_2 (&5:int))
         (r_1 * r_8) in
     let m_6 =
       update m_5 (shift a_2 (&6:int))
         (r_10 * r_7 + r_1 * r_3) in
     let m_7 =
       update m_6 (shift a_2 (&7:int))
         (r_10 * r_3 + --(r_1 * r_7)) in
     let m_8 =
       update m_7 (shift a_2 (&8:int))
         (r_6 * r_8) in
     region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> r_1 <= (&1:real)
     ==> r_3 <= (&1:real)
     ==> r_5 <= (&1:real)
     ==> r_6 <= (&1:real)
     ==> r_7 <= (&1:real)
     ==> r_8 <= (&1:real)
     ==> --(&1:real) <= r_1
     ==> --(&1:real) <= r_3
     ==> --(&1:real) <= r_5
     ==> --(&1:real) <= r_6
     ==> --(&1:real) <= r_7
     ==> --(&1:real) <= r_8
     ==> linked t
     ==> valid_rw t a (&9:int)
     ==> rvalid_floateulers t t_1 a_1
     ==> finite32 r
     ==> finite32 r_2
     ==> finite32 r_4
     ==> is_float32 r
     ==> is_float32 r_2
     ==> is_float32 r_4
     ==> finite32 r_1
     ==> finite32 r_3
     ==> finite32 r_5
     ==> finite32 r_6
     ==> finite32 r_7
     ==> finite32 r_8
     ==> is_float32 r_1
     ==> is_float32 r_3
     ==> is_float32 r_5
     ==> is_float32 r_6
     ==> is_float32 r_7
     ==> is_float32 r_8
     ==> rotation_matrix (matrix_of_memory m_8 a)`;;
