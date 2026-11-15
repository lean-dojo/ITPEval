(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_trace_pos_post_goal12:
  the trace-positive branch of converting a special orthogonal 3-by-3 real
  rotation matrix stored in memory to a quaternion. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !is_float32 finite32:real->bool.
   !a a_1:int#int.
   !t_1 t_8 t_7 t_4 t_6 t_5 t_9 t_2 t_3:(int#int)->real.
   !r_3 r_7 r_6 r_2 r_1 r_5 r r_4:real.
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
     let a_2 = shift a (&0:int) in
     let a_3 = shift a_2 (&0:int) in
     let r_8 = t_1 a_3 in
     let a_4 = shift a_2 (&4:int) in
     let r_9 = t_1 a_4 in
     let a_5 = shift a_2 (&8:int) in
     let r_10 = t_1 a_5 in
     let r_11 = r_8 + r_9 + r_10 in
     let a_7 = shift a_1 (&0:int) in
     let m = update t_8 a_7 ((&1 / &2) * r_3) in
     let a_8 = shift a_1 (&1:int) in
     let a_9 = shift a_2 (&5:int) in
     let a_10 = shift a_2 (&7:int) in
     let m_1 = update m a_8 ((m a_9 - m a_10) / r_7) in
     let a_11 = shift a_1 (&2:int) in
     let a_12 = shift a_2 (&6:int) in
     let a_13 = shift a_2 (&2:int) in
     let m_2 = update m_1 a_11 ((m_1 a_12 - m_1 a_13) / r_7) in
     let a_14 = shift a_1 (&3:int) in
     let a_15 = shift a_2 (&1:int) in
     let a_16 = shift a_2 (&3:int) in
     let r_13 = &1 + (t_8 a_3 + t_8 a_4 + t_8 a_5) in
     let m_3 =
       update
         (update t_7 a_7 ((t_7 a_9 - t_7 a_10) / r_6))
         a_8 ((&1 / &2) * r_2) in
     let m_4 = update m_3 a_11 ((m_3 a_15 + m_3 a_16) / r_6) in
     let r_15 = t_7 a_3 - t_7 a_4 - t_7 a_5 + &1 in
     let r_16 = t_4 a_5 in
     let r_17 = t_4 a_4 in
     let r_19 = &2 * r_1 in
     let m_5 = update t_6 a_7 ((t_6 a_12 - t_6 a_13) / r_5) in
     let m_6 =
       update
         (update m_5 a_8 ((m_5 a_15 + m_5 a_16) / r_5))
         a_11 ((&1 / &2) * r_1) in
     let m_7 = update m_6 a_14 ((m_6 a_9 + m_6 a_10) / r_5) in
     let r_20 = t_6 a_4 - t_6 a_3 - t_6 a_5 + &1 in
     let r_22 = &2 * r in
     let m_8 = update t_5 a_7 ((t_5 a_15 - t_5 a_16) / r_4) in
     let m_9 = update m_8 a_8 ((m_8 a_12 + m_8 a_13) / r_4) in
     let m_10 =
       update
         (update m_9 a_11 ((m_9 a_9 + m_9 a_10) / r_4))
         a_14 ((&1 / &2) * r) in
     let r_23 = t_5 a_5 - t_5 a_3 - t_5 a_4 + &1 in
     let finite_rmat =
       (finite32 (t_1 a_3) /\
        finite32 (t_1 a_15) /\
        finite32 (t_1 a_13) /\
        finite32 (t_1 a_16) /\
        finite32 (t_1 a_4) /\
        finite32 (t_1 a_9) /\
        finite32 (t_1 a_12) /\
        finite32 (t_1 a_10) /\
        finite32 (t_1 a_5)) in
     let rotation_matrix =
       (
       t_1 a_3 * t_1 a_3 +
         t_1 a_15 * t_1 a_15 +
         t_1 a_13 * t_1 a_13 = &1 /\
       t_1 a_3 * t_1 a_16 +
         t_1 a_15 * t_1 a_4 +
         t_1 a_13 * t_1 a_9 = &0 /\
       t_1 a_3 * t_1 a_12 +
         t_1 a_15 * t_1 a_10 +
         t_1 a_13 * t_1 a_5 = &0 /\
       t_1 a_16 * t_1 a_3 +
         t_1 a_4 * t_1 a_15 +
         t_1 a_9 * t_1 a_13 = &0 /\
       t_1 a_16 * t_1 a_16 +
         t_1 a_4 * t_1 a_4 +
         t_1 a_9 * t_1 a_9 = &1 /\
       t_1 a_16 * t_1 a_12 +
         t_1 a_4 * t_1 a_10 +
         t_1 a_9 * t_1 a_5 = &0 /\
       t_1 a_12 * t_1 a_3 +
         t_1 a_10 * t_1 a_15 +
         t_1 a_5 * t_1 a_13 = &0 /\
       t_1 a_12 * t_1 a_16 +
         t_1 a_10 * t_1 a_4 +
         t_1 a_5 * t_1 a_9 = &0 /\
       t_1 a_12 * t_1 a_12 +
         t_1 a_10 * t_1 a_10 +
         t_1 a_5 * t_1 a_5 = &1) in
     let special_orthogonal =
       (
       t_1 a_3 * t_1 a_4 * t_1 a_5 +
       t_1 a_15 * t_1 a_9 * t_1 a_12 +
       t_1 a_13 * t_1 a_16 * t_1 a_10 -
       t_1 a_3 * t_1 a_9 * t_1 a_10 -
       t_1 a_15 * t_1 a_16 * t_1 a_5 -
       t_1 a_13 * t_1 a_4 * t_1 a_12 = &1) in
     (!x:real. is_float32 x) /\
     (!x:real. finite32 x)
     ==> &0 < t_1 a_3 + t_1 a_4 + t_1 a_5
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> is_float32 r
     ==> is_float32 r_1
     ==> is_float32 r_2
     ==> is_float32 r_3
     ==> is_float32 r_4
     ==> is_float32 r_5
     ==> is_float32 r_6
     ==> is_float32 r_7
     ==> valid_rw t a_1 (&4:int)
     ==> finite_rmat /\ valid_rd t a (&9:int)
     ==> separated a (&9:int) a_1 (&4:int)
     ==> rotation_matrix
     ==> special_orthogonal
     ==> is_float32 r_8
     ==> is_float32 r_9
     ==> is_float32 r_10
     ==> is_float32 r_11
     ==> (if &0 < r_11 then
            t_8 = t_1 /\
            &2 * r_3 = r_7 /\
            update m_2 a_14 ((m_2 a_15 - m_2 a_16) / r_7) = t_9 /\
            &0 <= r_3 /\
            &0 <= r_13 /\
            finite32 r_3 /\
            finite32 r_13
          else
            t_2 = t_1 /\
            (if t_2 a_4 < t_2 a_3 then
               t_3 = t_2 /\
               (if t_3 a_5 < t_3 a_3 then
                  t_7 = t_3 /\
                  &2 * r_2 = r_6 /\
                  update m_4 a_14 ((m_4 a_12 + m_4 a_13) / r_6) =
                    t_9 /\
                  &0 <= r_2 /\
                  &0 <= r_15 /\
                  finite32 r_2 /\
                  finite32 r_15
                else
                  t_4 = t_3 /\
                  (if r_16 < r_17 then
                     t_6 = t_4 /\
                     r_19 = r_5 /\
                     m_7 = t_9 /\
                     &0 <= r_1 /\
                     &0 <= r_20 /\
                     finite32 r_1 /\
                     finite32 r_20
                   else
                     t_5 = t_4 /\
                     r_22 = r_4 /\
                     m_10 = t_9 /\
                     &0 <= r /\
                     &0 <= r_23 /\
                     finite32 r /\
                     finite32 r_23))
             else
               t_4 = t_2 /\
               (if r_16 < r_17 then
                  t_6 = t_4 /\
                  r_19 = r_5 /\
                  m_7 = t_9 /\
                  &0 <= r_1 /\
                  &0 <= r_20 /\
                  finite32 r_1 /\
                  finite32 r_20
                else
                  t_5 = t_4 /\
                  r_22 = r_4 /\
                  m_10 = t_9 /\
                  &0 <= r /\
                  &0 <= r_23 /\
                  finite32 r /\
                  finite32 r_23)))
     ==> r_3 = sqrt r_13
     ==> let qscale =
           (&1 / &2) / sqrt (&1 + t_9 a_3 + t_9 a_4 + t_9 a_5) in
         t_9 a_7 = (&1 / &4) / qscale /\
         t_9 a_8 = (t_9 a_9 - t_9 a_10) * qscale /\
         t_9 a_11 = (t_9 a_12 - t_9 a_13) * qscale /\
         t_9 a_14 = (t_9 a_15 - t_9 a_16) * qscale`;;
