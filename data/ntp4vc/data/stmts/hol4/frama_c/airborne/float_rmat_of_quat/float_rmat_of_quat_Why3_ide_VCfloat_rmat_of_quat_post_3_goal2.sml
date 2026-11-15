(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_of_quat/float_rmat_of_quat_Why3_ide_VCfloat_rmat_of_quat_post_3_goal2:
  a unit real quaternion is converted by nine functional memory updates into
  a 3-by-3 matrix whose determinant is one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_rmat_of_quat_Why3_ide_VCfloat_rmat_of_quat_post_3_goal2 =
  ``let froq_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let froq_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let froq_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let froq_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let froq_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let froq_is_float32 = \x : real. T in
    let froq_is_finite32 = \x : real. T in
    let froq_rvalid_floatquat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \q : int # int.
        froq_is_finite32 (mflt (froq_shift q 0)) /\
        froq_is_finite32 (mflt (froq_shift q 1)) /\
        froq_is_finite32 (mflt (froq_shift q 2)) /\
        froq_is_finite32 (mflt (froq_shift q 3)) /\
        froq_valid_rd malloc q 4
    in
    let froq_unitary_quaternion =
      \mflt : (int # int) -> real. \q : int # int.
        mflt (froq_shift q 0) * mflt (froq_shift q 0) +
        mflt (froq_shift q 1) * mflt (froq_shift q 1) +
        mflt (froq_shift q 2) * mflt (froq_shift q 2) +
        mflt (froq_shift q 3) * mflt (froq_shift q 3) = 1
    in
    let froq_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (froq_shift p 0),
         (mflt (froq_shift p 1),
          (mflt (froq_shift p 2),
           (mflt (froq_shift p 3),
            (mflt (froq_shift p 4),
             (mflt (froq_shift p 5),
              (mflt (froq_shift p 6),
               (mflt (froq_shift p 7), mflt (froq_shift p 8)))))))))
    in
    let froq_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let froq_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let froq_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let froq_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let froq_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let froq_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let froq_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let froq_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let froq_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let froq_special_orthogonal =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        froq_m00 m * froq_m11 m * froq_m22 m +
          froq_m01 m * froq_m12 m * froq_m20 m +
          froq_m02 m * froq_m10 m * froq_m21 m -
          froq_m00 m * froq_m12 m * froq_m21 m -
          froq_m01 m * froq_m10 m * froq_m22 m -
          froq_m02 m * froq_m11 m * froq_m20 m = 1
    in
      !t_1 : (int # int) -> real.
      !a_1 a : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let r = t_1 (froq_shift a_1 0) in
        let r_1 = t_1 (froq_shift a_1 1) in
        let r_2 = t_1 (froq_shift a_1 2) in
        let r_3 = t_1 (froq_shift a_1 3) in
        let r_4 = 2 * r in
        let r_5 = 2 * r_1 in
        let r_6 = 2 * r_3 in
        let r_7 = r_4 * r_1 in
        let r_8 = r_4 * r_2 in
        let r_9 = r_4 * r_3 in
        let r_10 = r_5 * r_2 in
        let r_11 = r_5 * r_3 in
        let r_12 = r_2 * r_6 in
        let r_13 = r_4 * r + -1 in
        let a_2 = froq_shift a 0 in
        let m =
          froq_update t_1 (froq_shift a_2 0)
            (r_13 + r_5 * r_1)
        in
        let m_1 =
          froq_update m (froq_shift a_2 1) (r_10 + r_9)
        in
        let m_2 =
          froq_update m_1 (froq_shift a_2 2) (r_11 + -r_8)
        in
        let m_3 =
          froq_update m_2 (froq_shift a_2 3) (r_10 + -r_9)
        in
        let m_4 =
          froq_update m_3 (froq_shift a_2 4)
            (r_13 + 2 * r_2 * r_2)
        in
        let m_5 =
          froq_update m_4 (froq_shift a_2 5) (r_12 + r_7)
        in
        let m_6 =
          froq_update m_5 (froq_shift a_2 6) (r_11 + r_8)
        in
        let m_7 =
          froq_update m_6 (froq_shift a_2 7) (r_12 + -r_7)
        in
        let m_8 =
          froq_update m_7 (froq_shift a_2 8)
            (r_13 + r_6 * r_3)
        in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          linked t ==>
          froq_unitary_quaternion t_1 a_1 ==>
          froq_valid_rw t a 9 ==>
          froq_rvalid_floatquat t t_1 a_1 ==>
          froq_separated a 9 a_1 4 ==>
          froq_is_float32 r ==>
          froq_is_float32 r_1 ==>
          froq_is_float32 r_2 ==>
          froq_is_float32 r_3 ==>
          froq_is_float32 r_4 ==>
          froq_is_float32 r_5 ==>
          froq_is_float32 r_6 ==>
          froq_is_float32 r_7 ==>
          froq_is_float32 r_8 ==>
          froq_is_float32 r_9 ==>
          froq_is_float32 r_10 ==>
          froq_is_float32 r_11 ==>
          froq_is_float32 r_12 ==>
          froq_is_float32 r_13 ==>
          froq_special_orthogonal (froq_rmat_of_mem m_8 a)``;
