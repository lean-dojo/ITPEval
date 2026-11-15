(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a22_max_post_goal11:
  the a22-diagonal-maximum branch of a real rotation-matrix conversion
  writes the corresponding quaternion components to valid separated memory.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val goal11 =
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
    let vcfc_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let vcfc_is_float32 = \x : real. T in
    let vcfc_is_finite32 = \x : real. T in
    let vcfc_rvalid_floatrmat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        vcfc_is_finite32 (mflt (vcfc_shift p 0)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 1)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 2)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 3)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 4)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 5)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 6)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 7)) /\
        vcfc_is_finite32 (mflt (vcfc_shift p 8)) /\
        vcfc_valid_rd malloc p 9
    in
    let vcfc_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (vcfc_shift p 0),
         (mflt (vcfc_shift p 1),
          (mflt (vcfc_shift p 2),
           (mflt (vcfc_shift p 3),
            (mflt (vcfc_shift p 4),
             (mflt (vcfc_shift p 5),
              (mflt (vcfc_shift p 6),
               (mflt (vcfc_shift p 7), mflt (vcfc_shift p 8)))))))))
    in
    let vcfc_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let vcfc_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let vcfc_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let vcfc_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let vcfc_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let vcfc_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let vcfc_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let vcfc_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let vcfc_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let vcfc_rotation_matrix =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        vcfc_m00 m * vcfc_m00 m +
            vcfc_m01 m * vcfc_m01 m +
            vcfc_m02 m * vcfc_m02 m = 1 /\
        vcfc_m00 m * vcfc_m10 m +
            vcfc_m01 m * vcfc_m11 m +
            vcfc_m02 m * vcfc_m12 m = 0 /\
        vcfc_m00 m * vcfc_m20 m +
            vcfc_m01 m * vcfc_m21 m +
            vcfc_m02 m * vcfc_m22 m = 0 /\
        vcfc_m10 m * vcfc_m00 m +
            vcfc_m11 m * vcfc_m01 m +
            vcfc_m12 m * vcfc_m02 m = 0 /\
        vcfc_m10 m * vcfc_m10 m +
            vcfc_m11 m * vcfc_m11 m +
            vcfc_m12 m * vcfc_m12 m = 1 /\
        vcfc_m10 m * vcfc_m20 m +
            vcfc_m11 m * vcfc_m21 m +
            vcfc_m12 m * vcfc_m22 m = 0 /\
        vcfc_m20 m * vcfc_m00 m +
            vcfc_m21 m * vcfc_m01 m +
            vcfc_m22 m * vcfc_m02 m = 0 /\
        vcfc_m20 m * vcfc_m10 m +
            vcfc_m21 m * vcfc_m11 m +
            vcfc_m22 m * vcfc_m12 m = 0 /\
        vcfc_m20 m * vcfc_m20 m +
            vcfc_m21 m * vcfc_m21 m +
            vcfc_m22 m * vcfc_m22 m = 1
    in
    let vcfc_special_orthogonal =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        vcfc_m00 m * vcfc_m11 m * vcfc_m22 m +
          vcfc_m01 m * vcfc_m12 m * vcfc_m20 m +
          vcfc_m02 m * vcfc_m10 m * vcfc_m21 m -
          vcfc_m00 m * vcfc_m12 m * vcfc_m21 m -
          vcfc_m01 m * vcfc_m10 m * vcfc_m22 m -
          vcfc_m02 m * vcfc_m11 m * vcfc_m20 m = 1
    in
    let vcfc_trace =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        vcfc_m00 m + vcfc_m11 m + vcfc_m22 m
    in
    let vcfc_floatquat_2_max_t =
      \mflt : (int # int) -> real. \p : int # int.
        let m = vcfc_rmat_of_mem mflt p in
        let z =
          sqrt (1 + vcfc_m22 m - vcfc_m00 m - vcfc_m11 m)
        in
        let two_z = 2 * z in
          ((vcfc_m01 m - vcfc_m10 m) / two_z,
           ((vcfc_m20 m + vcfc_m02 m) / two_z,
            ((vcfc_m21 m + vcfc_m12 m) / two_z,
             1 / 2 * z)))
    in
    let vcfc_quat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (vcfc_shift p 0),
         (mflt (vcfc_shift p 1),
          (mflt (vcfc_shift p 2), mflt (vcfc_shift p 3))))
    in
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a : int # int.
      !t_1 : (int # int) -> real.
      !a_1 : int # int.
      !t_8 : (int # int) -> real.
      !r_3 r_7 : real.
      !t_7 : (int # int) -> real.
      !r_6 r_2 : real.
      !t_4 : (int # int) -> real.
      !r_1 : real.
      !t_6 : (int # int) -> real.
      !r_5 r : real.
      !t_5 : (int # int) -> real.
      !r_4 : real.
      !t : int -> int.
      !t_9 t_2 t_3 : (int # int) -> real.
        let a_2 = vcfc_shift a 0 in
        let a_3 = vcfc_shift a_2 0 in
        let r_8 = t_1 a_3 in
        let a_4 = vcfc_shift a_2 8 in
        let r_9 = t_1 a_4 in
        let a_5 = vcfc_shift a_2 4 in
        let r_10 = t_1 a_5 in
        let a_6 = vcfc_rmat_of_mem t_1 a in
        let r_11 = r_8 + r_10 + r_9 in
        let a_7 = vcfc_shift a_1 0 in
        let m = vcfc_update t_8 a_7 (1 / 2 * r_3) in
        let a_8 = vcfc_shift a_1 1 in
        let a_9 = vcfc_shift a_2 5 in
        let a_10 = vcfc_shift a_2 7 in
        let m_1 =
          vcfc_update m a_8 ((m a_9 + -(m a_10)) / r_7)
        in
        let a_11 = vcfc_shift a_1 2 in
        let a_12 = vcfc_shift a_2 6 in
        let a_13 = vcfc_shift a_2 2 in
        let m_2 =
          vcfc_update m_1 a_11
            ((m_1 a_12 + -(m_1 a_13)) / r_7)
        in
        let a_14 = vcfc_shift a_1 3 in
        let a_15 = vcfc_shift a_2 1 in
        let a_16 = vcfc_shift a_2 3 in
        let r_13 = 1 + (t_8 a_3 + t_8 a_5 + t_8 a_4) in
        let m_3 =
          vcfc_update
            (vcfc_update t_7 a_7
              ((t_7 a_9 + -(t_7 a_10)) / r_6))
            a_8 (1 / 2 * r_2)
        in
        let m_4 =
          vcfc_update m_3 a_11 ((m_3 a_15 + m_3 a_16) / r_6)
        in
        let r_15 = t_7 a_3 + -(t_7 a_5) + -(t_7 a_4) + 1 in
        let r_16 = t_4 a_4 in
        let r_17 = t_4 a_5 in
        let r_19 = 2 * r_1 in
        let m_5 =
          vcfc_update t_6 a_7
            ((t_6 a_12 + -(t_6 a_13)) / r_5)
        in
        let m_6 =
          vcfc_update
            (vcfc_update m_5 a_8 ((m_5 a_15 + m_5 a_16) / r_5))
            a_11 (1 / 2 * r_1)
        in
        let m_7 =
          vcfc_update m_6 a_14 ((m_6 a_9 + m_6 a_10) / r_5)
        in
        let r_20 = t_6 a_5 + -(t_6 a_3) + -(t_6 a_4) + 1 in
        let r_22 = 2 * r in
        let m_8 =
          vcfc_update t_5 a_7
            ((t_5 a_15 + -(t_5 a_16)) / r_4)
        in
        let m_9 =
          vcfc_update m_8 a_8 ((m_8 a_12 + m_8 a_13) / r_4)
        in
        let m_10 =
          vcfc_update
            (vcfc_update m_9 a_11 ((m_9 a_9 + m_9 a_10) / r_4))
            a_14 (1 / 2 * r)
        in
        let r_23 = t_5 a_4 + -(t_5 a_3) + -(t_5 a_5) + 1 in
          vcfc_trace a_6 <= 0 ==>
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          r_8 <= r_9 ==>
          r_10 <= r_9 ==>
          linked t ==>
          vcfc_is_float32 r ==>
          vcfc_is_float32 r_1 ==>
          vcfc_is_float32 r_2 ==>
          vcfc_is_float32 r_3 ==>
          vcfc_is_float32 r_4 ==>
          vcfc_is_float32 r_5 ==>
          vcfc_is_float32 r_6 ==>
          vcfc_is_float32 r_7 ==>
          vcfc_valid_rw t a_1 4 ==>
          vcfc_rvalid_floatrmat t t_1 a ==>
          vcfc_separated a 9 a_1 4 ==>
          vcfc_rotation_matrix a_6 ==>
          vcfc_special_orthogonal a_6 ==>
          vcfc_is_float32 r_8 ==>
          vcfc_is_float32 r_10 ==>
          vcfc_is_float32 r_9 ==>
          vcfc_is_float32 r_11 ==>
          (if 0 < r_11 then
             t_8 = t_1 /\
             2 * r_3 = r_7 /\
             vcfc_update m_2 a_14
               ((m_2 a_15 + -(m_2 a_16)) / r_7) = t_9 /\
             0 <= r_3 /\
             0 <= r_13 /\
             vcfc_is_finite32 r_3 /\
             vcfc_is_finite32 r_13
           else
             t_2 = t_1 /\
             (if t_2 a_5 < t_2 a_3 then
                t_3 = t_2 /\
                (if t_3 a_4 < t_3 a_3 then
                   t_7 = t_3 /\
                   2 * r_2 = r_6 /\
                   vcfc_update m_4 a_14
                     ((m_4 a_12 + m_4 a_13) / r_6) = t_9 /\
                   0 <= r_2 /\
                   0 <= r_15 /\
                   vcfc_is_finite32 r_2 /\
                   vcfc_is_finite32 r_15
                 else
                   t_4 = t_3 /\
                   (if r_16 < r_17 then
                      t_6 = t_4 /\
                      r_19 = r_5 /\
                      m_7 = t_9 /\
                      0 <= r_1 /\
                      0 <= r_20 /\
                      vcfc_is_finite32 r_1 /\
                      vcfc_is_finite32 r_20
                    else
                      t_5 = t_4 /\
                      r_22 = r_4 /\
                      m_10 = t_9 /\
                      0 <= r /\
                      0 <= r_23 /\
                      vcfc_is_finite32 r /\
                      vcfc_is_finite32 r_23))
              else
                t_4 = t_2 /\
                (if r_16 < r_17 then
                   t_6 = t_4 /\
                   r_19 = r_5 /\
                   m_7 = t_9 /\
                   0 <= r_1 /\
                   0 <= r_20 /\
                   vcfc_is_finite32 r_1 /\
                   vcfc_is_finite32 r_20
                 else
                   t_5 = t_4 /\
                   r_22 = r_4 /\
                   m_10 = t_9 /\
                   0 <= r /\
                   0 <= r_23 /\
                   vcfc_is_finite32 r /\
                   vcfc_is_finite32 r_23))) ==>
          vcfc_floatquat_2_max_t t_9 a =
            vcfc_quat_of_mem t_9 a_1``;
