(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_comp/float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0:
  four component writes compute the Hamilton product of two real quaternions
  stored in separated valid memory regions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0 =
  ``let vcfc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let vcfc_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let vcfc_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let vcfc_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let vcfc_is_finite32 = \x : real. T in
    let vcfc_is_float32 = \x : real. T in
    let vcfc_rvalid_floatquat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \q : int # int.
        vcfc_is_finite32 (mflt (vcfc_shift q 0)) /\
        vcfc_is_finite32 (mflt (vcfc_shift q 1)) /\
        vcfc_is_finite32 (mflt (vcfc_shift q 2)) /\
        vcfc_is_finite32 (mflt (vcfc_shift q 3)) /\
        vcfc_valid_rd malloc q 4
    in
    let vcfc_quat_of_mem =
      \mflt : (int # int) -> real. \q : int # int.
        (mflt (vcfc_shift q 0),
         (mflt (vcfc_shift q 1),
          (mflt (vcfc_shift q 2), mflt (vcfc_shift q 3))))
    in
    let vcfc_qscalar =
      \q : (real # (real # (real # real))). FST q
    in
    let vcfc_qx =
      \q : (real # (real # (real # real))). FST (SND q)
    in
    let vcfc_qy =
      \q : (real # (real # (real # real))). FST (SND (SND q))
    in
    let vcfc_qz =
      \q : (real # (real # (real # real))). SND (SND (SND q))
    in
    let vcfc_quat_mul =
      \q1 q2 : real # (real # (real # real)).
        (-(vcfc_qx q1 * vcfc_qx q2 +
            vcfc_qy q1 * vcfc_qy q2 +
            vcfc_qz q1 * vcfc_qz q2) +
           vcfc_qscalar q1 * vcfc_qscalar q2,
         (vcfc_qscalar q1 * vcfc_qx q2 +
            vcfc_qscalar q2 * vcfc_qx q1 +
            (-(vcfc_qz q1 * vcfc_qy q2) +
             vcfc_qy q1 * vcfc_qz q2),
          (vcfc_qscalar q1 * vcfc_qy q2 +
             vcfc_qscalar q2 * vcfc_qy q1 +
             (-(vcfc_qx q1 * vcfc_qz q2) +
              vcfc_qz q1 * vcfc_qx q2),
           vcfc_qscalar q1 * vcfc_qz q2 +
             vcfc_qscalar q2 * vcfc_qz q1 +
             (-(vcfc_qy q1 * vcfc_qx q2) +
              vcfc_qx q1 * vcfc_qy q2))))
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a_1 a a_2 : int # int.
      !t_1 : (int # int) -> real.
      !t : int -> int.
        let a_3 = vcfc_shift a_1 0 in
        let a_4 = vcfc_shift a 0 in
        let a_5 = vcfc_shift a_2 0 in
        let a_6 = vcfc_shift a 1 in
        let a_7 = vcfc_shift a_1 1 in
        let a_8 = vcfc_shift a_2 1 in
        let a_9 = vcfc_shift a 2 in
        let a_10 = vcfc_shift a_1 2 in
        let a_11 = vcfc_shift a_2 2 in
        let a_12 = vcfc_shift a 3 in
        let a_13 = vcfc_shift a_1 3 in
        let a_14 = vcfc_shift a_2 3 in
        let r = t_1 a_4 in
        let r_1 = t_1 a_5 in
        let r_2 = t_1 a_6 in
        let r_3 = t_1 a_8 in
        let r_4 = t_1 a_9 in
        let r_5 = t_1 a_11 in
        let r_6 = t_1 a_12 in
        let r_7 = t_1 a_14 in
        let m =
          vcfc_update t_1 a_3
            (r_1 * r + -(r_3 * r_2) + -(r_5 * r_4) + -(r_7 * r_6))
        in
        let r_8 = m a_4 in
        let r_9 = m a_5 in
        let r_10 = m a_6 in
        let r_11 = m a_8 in
        let r_12 = m a_9 in
        let r_13 = m a_11 in
        let r_14 = m a_12 in
        let r_15 = m a_14 in
        let m_1 =
          vcfc_update m a_7
            (r_9 * r_10 + r_11 * r_8 + r_13 * r_14 + -(r_15 * r_12))
        in
        let r_16 = m_1 a_4 in
        let r_17 = m_1 a_5 in
        let r_18 = m_1 a_6 in
        let r_19 = m_1 a_8 in
        let r_20 = m_1 a_9 in
        let r_21 = m_1 a_11 in
        let r_22 = m_1 a_12 in
        let r_23 = m_1 a_14 in
        let m_2 =
          vcfc_update m_1 a_10
            (r_17 * r_20 + -(r_19 * r_22) + r_21 * r_16 +
             r_23 * r_18)
        in
        let r_24 = m_2 a_4 in
        let r_25 = m_2 a_5 in
        let r_26 = m_2 a_6 in
        let r_27 = m_2 a_8 in
        let r_28 = m_2 a_9 in
        let r_29 = m_2 a_11 in
        let r_30 = m_2 a_12 in
        let r_31 = m_2 a_14 in
        let m_3 =
          vcfc_update m_2 a_13
            (r_25 * r_30 + r_27 * r_28 + -(r_29 * r_26) +
             r_31 * r_24)
        in
          a_3 <> a_4 ==>
          a_5 <> a_4 ==>
          a_5 <> a_3 ==>
          a_6 <> a_3 ==>
          a_6 <> a_5 ==>
          a_7 <> a_4 ==>
          a_7 <> a_5 ==>
          a_7 <> a_6 ==>
          a_8 <> a_4 ==>
          a_8 <> a_3 ==>
          a_8 <> a_6 ==>
          a_8 <> a_7 ==>
          a_9 <> a_3 ==>
          a_9 <> a_5 ==>
          a_9 <> a_7 ==>
          a_9 <> a_8 ==>
          a_10 <> a_4 ==>
          a_10 <> a_5 ==>
          a_10 <> a_6 ==>
          a_10 <> a_8 ==>
          a_10 <> a_9 ==>
          a_11 <> a_4 ==>
          a_11 <> a_3 ==>
          a_11 <> a_6 ==>
          a_11 <> a_7 ==>
          a_11 <> a_9 ==>
          a_11 <> a_10 ==>
          a_12 <> a_3 ==>
          a_12 <> a_5 ==>
          a_12 <> a_7 ==>
          a_12 <> a_8 ==>
          a_12 <> a_10 ==>
          a_12 <> a_11 ==>
          a_13 <> a_4 ==>
          a_13 <> a_5 ==>
          a_13 <> a_6 ==>
          a_13 <> a_8 ==>
          a_13 <> a_9 ==>
          a_13 <> a_11 ==>
          a_13 <> a_12 ==>
          a_14 <> a_4 ==>
          a_14 <> a_3 ==>
          a_14 <> a_6 ==>
          a_14 <> a_7 ==>
          a_14 <> a_9 ==>
          a_14 <> a_10 ==>
          a_14 <> a_12 ==>
          a_14 <> a_13 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          linked t ==>
          vcfc_valid_rw t a_1 4 ==>
          vcfc_rvalid_floatquat t t_1 a ==>
          vcfc_rvalid_floatquat t t_1 a_2 ==>
          vcfc_is_float32 r ==>
          vcfc_is_float32 r_1 ==>
          vcfc_is_float32 r_2 ==>
          vcfc_is_float32 r_3 ==>
          vcfc_is_float32 r_4 ==>
          vcfc_is_float32 r_5 ==>
          vcfc_is_float32 r_6 ==>
          vcfc_is_float32 r_7 ==>
          vcfc_is_float32 r_8 ==>
          vcfc_is_float32 r_9 ==>
          vcfc_is_float32 r_10 ==>
          vcfc_is_float32 r_11 ==>
          vcfc_is_float32 r_12 ==>
          vcfc_is_float32 r_13 ==>
          vcfc_is_float32 r_14 ==>
          vcfc_is_float32 r_15 ==>
          vcfc_is_float32 r_16 ==>
          vcfc_is_float32 r_17 ==>
          vcfc_is_float32 r_18 ==>
          vcfc_is_float32 r_19 ==>
          vcfc_is_float32 r_20 ==>
          vcfc_is_float32 r_21 ==>
          vcfc_is_float32 r_22 ==>
          vcfc_is_float32 r_23 ==>
          vcfc_is_float32 r_24 ==>
          vcfc_is_float32 r_25 ==>
          vcfc_is_float32 r_26 ==>
          vcfc_is_float32 r_27 ==>
          vcfc_is_float32 r_28 ==>
          vcfc_is_float32 r_29 ==>
          vcfc_is_float32 r_30 ==>
          vcfc_is_float32 r_31 ==>
          vcfc_quat_of_mem m_3 a_1 =
            vcfc_quat_mul
              (vcfc_quat_of_mem m_3 a_2)
              (vcfc_quat_of_mem m_3 a)``;
