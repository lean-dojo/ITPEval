(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_of_quat/float_rmat_of_quat_Why3_ide_VCfloat_rmat_of_quat_post_2_goal1:
  the nine matrix entries computed from a unit quaternion form a real rotation
  matrix under the source memory, separation, and floating-point assumptions.
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
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let finite32 = \x:real. T in
     let is_float32 = \x:real. T in
     let finite_floatquat =
       \(mem:(int#int)->real) (q:int#int).
         finite32 (mem (shift q (&0:int))) /\
         finite32 (mem (shift q (&1:int))) /\
         finite32 (mem (shift q (&2:int))) /\
         finite32 (mem (shift q (&3:int))) in
     let rvalid_floatquat =
       \(malloc:int->int) (mem:(int#int)->real) (q:int#int).
         finite_floatquat mem q /\
         valid_rd malloc q (&4:int) in
     let unit_quaternion =
       \(mem:(int#int)->real) (q:int#int).
         let q0 = mem (shift q (&0:int)) in
         let q1 = mem (shift q (&1:int)) in
         let q2 = mem (shift q (&2:int)) in
         let q3 = mem (shift q (&3:int)) in
         q0 * q0 + q1 * q1 + q2 * q2 + q3 * q3 = (&1:real) in
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
       \(mat:(real#(real#real))#
             ((real#(real#real))#(real#(real#real)))).
         let row0 = FST mat in
         let row1 = FST (SND mat) in
         let row2 = SND (SND mat) in
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
     let r_1 = t_1 (shift a_1 (&1:int)) in
     let r_2 = t_1 (shift a_1 (&2:int)) in
     let r_3 = t_1 (shift a_1 (&3:int)) in
     let r_4 = (&2:real) * r in
     let r_5 = (&2:real) * r_1 in
     let r_6 = (&2:real) * r_3 in
     let r_7 = r_4 * r_1 in
     let r_8 = r_4 * r_2 in
     let r_9 = r_4 * r_3 in
     let r_10 = r_5 * r_2 in
     let r_11 = r_5 * r_3 in
     let r_12 = r_2 * r_6 in
     let r_13 = r_4 * r + --(&1:real) in
     let a_2 = shift a (&0:int) in
     let m_0 =
       update t_1 (shift a_2 (&0:int))
         (r_13 + r_5 * r_1) in
     let m_1 =
       update m_0 (shift a_2 (&1:int))
         (r_10 + r_9) in
     let m_2 =
       update m_1 (shift a_2 (&2:int))
         (r_11 + --r_8) in
     let m_3 =
       update m_2 (shift a_2 (&3:int))
         (r_10 + --r_9) in
     let m_4 =
       update m_3 (shift a_2 (&4:int))
         (r_13 + (&2:real) * r_2 * r_2) in
     let m_5 =
       update m_4 (shift a_2 (&5:int))
         (r_12 + r_7) in
     let m_6 =
       update m_5 (shift a_2 (&6:int))
         (r_11 + r_8) in
     let m_7 =
       update m_6 (shift a_2 (&7:int))
         (r_12 + --r_7) in
     let m_8 =
       update m_7 (shift a_2 (&8:int))
         (r_13 + r_6 * r_3) in
     region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> unit_quaternion t_1 a_1
     ==> valid_rw t a (&9:int)
     ==> rvalid_floatquat t t_1 a_1
     ==> separated a (&9:int) a_1 (&4:int)
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
     ==> rotation_matrix (matrix_of_memory m_8 a)`;;
