(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_comp/float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0:
  the memory updates performed by floating-point quaternion composition produce
  the modeled real quaternion product. This file contains no proof.
*)

let float_quat_comp_shift = new_definition
  `float_quat_comp_shift (p:int#int) (k:int) =
     (FST p,SND p + k)`;;

let float_quat_comp_valid_rw = new_definition
  `float_quat_comp_valid_rw (mem:int->int) (p:int#int) (n:int) <=>
     (&0:int) < n
     ==> (&0:int) < FST p /\
         (&0:int) <= SND p /\
         SND p + n <= mem (FST p)`;;

let float_quat_comp_valid_rd = new_definition
  `float_quat_comp_valid_rd (mem:int->int) (p:int#int) (n:int) <=>
     (&0:int) < n
     ==> ~(FST p = (&0:int)) /\
         (&0:int) <= SND p /\
         SND p + n <= mem (FST p)`;;

let float_quat_comp_is_finite32 = new_definition
  `float_quat_comp_is_finite32 (x:real) <=> T`;;

let float_quat_comp_is_float32 = new_definition
  `float_quat_comp_is_float32 (x:real) <=> T`;;

let float_quat_comp_p_finite_floatquat = new_definition
  `float_quat_comp_p_finite_floatquat
      (mem:(int#int)->real) (q:int#int) <=>
     float_quat_comp_is_finite32
       (mem (float_quat_comp_shift q (&0:int))) /\
     float_quat_comp_is_finite32
       (mem (float_quat_comp_shift q (&1:int))) /\
     float_quat_comp_is_finite32
       (mem (float_quat_comp_shift q (&2:int))) /\
     float_quat_comp_is_finite32
       (mem (float_quat_comp_shift q (&3:int)))`;;

let float_quat_comp_p_rvalid_floatquat = new_definition
  `float_quat_comp_p_rvalid_floatquat
      (malloc:int->int) (mem:(int#int)->real) (q:int#int) <=>
     float_quat_comp_p_finite_floatquat mem q /\
     float_quat_comp_valid_rd malloc q (&4:int)`;;

let float_quat_comp_quat_of_memory = new_definition
  `float_quat_comp_quat_of_memory
      (mem:(int#int)->real) (q:int#int) =
     (mem (float_quat_comp_shift q (&0:int)),
      (mem (float_quat_comp_shift q (&1:int)),
       (mem (float_quat_comp_shift q (&2:int)),
        mem (float_quat_comp_shift q (&3:int)))))`;;

let float_quat_comp_quat_mul = new_definition
  `float_quat_comp_quat_mul
      (q1:real#(real#(real#real))) (q2:real#(real#(real#real))) =
     let s1 = FST q1 in
     let x1 = FST (SND q1) in
     let y1 = FST (SND (SND q1)) in
     let z1 = SND (SND (SND q1)) in
     let s2 = FST q2 in
     let x2 = FST (SND q2) in
     let y2 = FST (SND (SND q2)) in
     let z2 = SND (SND (SND q2)) in
     (s1 * s2 + --(x1 * x2 + y1 * y2 + z1 * z2),
      (s1 * x2 + s2 * x1 + (y1 * z2 + --(z1 * y2)),
       (s1 * y2 + s2 * y1 + (z1 * x2 + --(x1 * z2)),
        s1 * z2 + s2 * z1 + (x1 * y2 + --(y1 * x2)))))`;;

let FLOAT_QUAT_COMP_WHY3_IDE_VCFLOAT_QUAT_COMP_POST_GOAL0 =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a_1 a a_2:int#int.
   !t_1:(int#int)->real.
   !t:int->int.
     let a_3 = float_quat_comp_shift a_1 (&0:int) in
     let a_4 = float_quat_comp_shift a (&0:int) in
     let a_5 = float_quat_comp_shift a_2 (&0:int) in
     let a_6 = float_quat_comp_shift a (&1:int) in
     let a_7 = float_quat_comp_shift a_1 (&1:int) in
     let a_8 = float_quat_comp_shift a_2 (&1:int) in
     let a_9 = float_quat_comp_shift a (&2:int) in
     let a_10 = float_quat_comp_shift a_1 (&2:int) in
     let a_11 = float_quat_comp_shift a_2 (&2:int) in
     let a_12 = float_quat_comp_shift a (&3:int) in
     let a_13 = float_quat_comp_shift a_1 (&3:int) in
     let a_14 = float_quat_comp_shift a_2 (&3:int) in
     let r = t_1 a_4 in
     let r_1 = t_1 a_5 in
     let r_2 = t_1 a_6 in
     let r_3 = t_1 a_8 in
     let r_4 = t_1 a_9 in
     let r_5 = t_1 a_11 in
     let r_6 = t_1 a_12 in
     let r_7 = t_1 a_14 in
     let m =
       (\p. if p = a_3
            then r_1 * r + --(r_3 * r_2) +
                 --(r_5 * r_4) + --(r_7 * r_6)
            else t_1 p) in
     let r_8 = m a_4 in
     let r_9 = m a_5 in
     let r_10 = m a_6 in
     let r_11 = m a_8 in
     let r_12 = m a_9 in
     let r_13 = m a_11 in
     let r_14 = m a_12 in
     let r_15 = m a_14 in
     let m_1 =
       (\p. if p = a_7
            then r_9 * r_10 + r_11 * r_8 +
                 r_13 * r_14 + --(r_15 * r_12)
            else m p) in
     let r_16 = m_1 a_4 in
     let r_17 = m_1 a_5 in
     let r_18 = m_1 a_6 in
     let r_19 = m_1 a_8 in
     let r_20 = m_1 a_9 in
     let r_21 = m_1 a_11 in
     let r_22 = m_1 a_12 in
     let r_23 = m_1 a_14 in
     let m_2 =
       (\p. if p = a_10
            then r_17 * r_20 + --(r_19 * r_22) +
                 r_21 * r_16 + r_23 * r_18
            else m_1 p) in
     let r_24 = m_2 a_4 in
     let r_25 = m_2 a_5 in
     let r_26 = m_2 a_6 in
     let r_27 = m_2 a_8 in
     let r_28 = m_2 a_9 in
     let r_29 = m_2 a_11 in
     let r_30 = m_2 a_12 in
     let r_31 = m_2 a_14 in
     let m_3 =
       (\p. if p = a_13
            then r_25 * r_30 + r_27 * r_28 +
                 --(r_29 * r_26) + r_31 * r_24
            else m_2 p) in
     ~(a_3 = a_4) ==>
     ~(a_5 = a_4) ==>
     ~(a_5 = a_3) ==>
     ~(a_6 = a_3) ==>
     ~(a_6 = a_5) ==>
     ~(a_7 = a_4) ==>
     ~(a_7 = a_5) ==>
     ~(a_7 = a_6) ==>
     ~(a_8 = a_4) ==>
     ~(a_8 = a_3) ==>
     ~(a_8 = a_6) ==>
     ~(a_8 = a_7) ==>
     ~(a_9 = a_3) ==>
     ~(a_9 = a_5) ==>
     ~(a_9 = a_7) ==>
     ~(a_9 = a_8) ==>
     ~(a_10 = a_4) ==>
     ~(a_10 = a_5) ==>
     ~(a_10 = a_6) ==>
     ~(a_10 = a_8) ==>
     ~(a_10 = a_9) ==>
     ~(a_11 = a_4) ==>
     ~(a_11 = a_3) ==>
     ~(a_11 = a_6) ==>
     ~(a_11 = a_7) ==>
     ~(a_11 = a_9) ==>
     ~(a_11 = a_10) ==>
     ~(a_12 = a_3) ==>
     ~(a_12 = a_5) ==>
     ~(a_12 = a_7) ==>
     ~(a_12 = a_8) ==>
     ~(a_12 = a_10) ==>
     ~(a_12 = a_11) ==>
     ~(a_13 = a_4) ==>
     ~(a_13 = a_5) ==>
     ~(a_13 = a_6) ==>
     ~(a_13 = a_8) ==>
     ~(a_13 = a_9) ==>
     ~(a_13 = a_11) ==>
     ~(a_13 = a_12) ==>
     ~(a_14 = a_4) ==>
     ~(a_14 = a_3) ==>
     ~(a_14 = a_6) ==>
     ~(a_14 = a_7) ==>
     ~(a_14 = a_9) ==>
     ~(a_14 = a_10) ==>
     ~(a_14 = a_12) ==>
     ~(a_14 = a_13) ==>
     region (FST a) <= (&0:int) ==>
     region (FST a_1) <= (&0:int) ==>
     region (FST a_2) <= (&0:int) ==>
     linked t ==>
     float_quat_comp_valid_rw t a_1 (&4:int) ==>
     float_quat_comp_p_rvalid_floatquat t t_1 a ==>
     float_quat_comp_p_rvalid_floatquat t t_1 a_2 ==>
     float_quat_comp_is_float32 r ==>
     float_quat_comp_is_float32 r_1 ==>
     float_quat_comp_is_float32 r_2 ==>
     float_quat_comp_is_float32 r_3 ==>
     float_quat_comp_is_float32 r_4 ==>
     float_quat_comp_is_float32 r_5 ==>
     float_quat_comp_is_float32 r_6 ==>
     float_quat_comp_is_float32 r_7 ==>
     float_quat_comp_is_float32 r_8 ==>
     float_quat_comp_is_float32 r_9 ==>
     float_quat_comp_is_float32 r_10 ==>
     float_quat_comp_is_float32 r_11 ==>
     float_quat_comp_is_float32 r_12 ==>
     float_quat_comp_is_float32 r_13 ==>
     float_quat_comp_is_float32 r_14 ==>
     float_quat_comp_is_float32 r_15 ==>
     float_quat_comp_is_float32 r_16 ==>
     float_quat_comp_is_float32 r_17 ==>
     float_quat_comp_is_float32 r_18 ==>
     float_quat_comp_is_float32 r_19 ==>
     float_quat_comp_is_float32 r_20 ==>
     float_quat_comp_is_float32 r_21 ==>
     float_quat_comp_is_float32 r_22 ==>
     float_quat_comp_is_float32 r_23 ==>
     float_quat_comp_is_float32 r_24 ==>
     float_quat_comp_is_float32 r_25 ==>
     float_quat_comp_is_float32 r_26 ==>
     float_quat_comp_is_float32 r_27 ==>
     float_quat_comp_is_float32 r_28 ==>
     float_quat_comp_is_float32 r_29 ==>
     float_quat_comp_is_float32 r_30 ==>
     float_quat_comp_is_float32 r_31 ==>
     float_quat_comp_quat_of_memory m_3 a_1 =
     float_quat_comp_quat_mul
       (float_quat_comp_quat_of_memory m_3 a_2)
       (float_quat_comp_quat_of_memory m_3 a)`;;
