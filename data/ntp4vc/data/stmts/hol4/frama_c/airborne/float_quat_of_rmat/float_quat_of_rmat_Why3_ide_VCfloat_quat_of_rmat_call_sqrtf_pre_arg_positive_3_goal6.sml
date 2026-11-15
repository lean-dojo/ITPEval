(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_arg_positive_3_goal6:
  nonnegativity of the square-root argument in a real rotation-matrix to
  quaternion conversion branch under its memory and matrix assumptions.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val goal6 =
  ``let vcfc_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
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
      !region : int -> int.
      !linked : (int -> int) -> bool.
      !a : int # int.
      !t_1 : (int # int) -> real.
      !a_1 : int # int.
      !t : int -> int.
        let a_2 = vcfc_shift a 0 in
        let r = t_1 (vcfc_shift a_2 8) in
        let r_1 = t_1 (vcfc_shift a_2 4) in
        let r_2 = t_1 (vcfc_shift a_2 0) in
        let r_3 = r_2 + r_1 + r in
        let a_3 = vcfc_rmat_of_mem t_1 a in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          r < r_1 ==>
          r_3 <= 0 ==>
          linked t ==>
          vcfc_valid_rw t a_1 4 ==>
          vcfc_rvalid_floatrmat t t_1 a ==>
          vcfc_separated a 9 a_1 4 ==>
          vcfc_rotation_matrix a_3 ==>
          vcfc_special_orthogonal a_3 ==>
          vcfc_is_float32 r_2 ==>
          vcfc_is_float32 (t_1 (vcfc_shift a_2 2)) ==>
          vcfc_is_float32 r_1 ==>
          vcfc_is_float32 (t_1 (vcfc_shift a_2 6)) ==>
          vcfc_is_float32 r ==>
          vcfc_is_float32 r_3 ==>
          (r_2 <= r_1 \/ r_2 <= r) ==>
          0 <= r_1 + -r_2 + -r + 1``;
