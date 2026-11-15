(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_of_eulers_321/float_rmat_of_eulers_321_Why3_ide_VCfloat_rmat_of_eulers_321_post_2_goal1:
  3-2-1 Euler-angle sine and cosine values are written into nine real memory
  entries whose resulting matrix has determinant one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory transcTheory;

val _ = new_theory "hello";

val float_rmat_of_eulers_321_Why3_ide_VCfloat_rmat_of_eulers_321_post_2_goal1 =
  ``let froe321_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let froe321_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let froe321_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let froe321_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let froe321_is_float32 = \x : real. T in
    let froe321_is_finite32 = \x : real. T in
    let froe321_rvalid_floateulers =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \e : int # int.
        froe321_is_finite32 (mflt (froe321_shift e 0)) /\
        froe321_is_finite32 (mflt (froe321_shift e 2)) /\
        froe321_is_finite32 (mflt (froe321_shift e 1)) /\
        froe321_valid_rd malloc e 3
    in
    let froe321_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (froe321_shift p 0),
         (mflt (froe321_shift p 1),
          (mflt (froe321_shift p 2),
           (mflt (froe321_shift p 3),
            (mflt (froe321_shift p 4),
             (mflt (froe321_shift p 5),
              (mflt (froe321_shift p 6),
               (mflt (froe321_shift p 7), mflt (froe321_shift p 8)))))))))
    in
    let froe321_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let froe321_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let froe321_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let froe321_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let froe321_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let froe321_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let froe321_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let froe321_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let froe321_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let froe321_special_orthogonal =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        froe321_m00 m * froe321_m11 m * froe321_m22 m +
        froe321_m01 m * froe321_m12 m * froe321_m20 m +
        froe321_m02 m * froe321_m10 m * froe321_m21 m -
        froe321_m00 m * froe321_m12 m * froe321_m21 m -
        froe321_m01 m * froe321_m10 m * froe321_m22 m -
        froe321_m02 m * froe321_m11 m * froe321_m20 m = 1
    in
      !t_1 : (int # int) -> real.
      !a_1 a : int # int.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let r = t_1 (froe321_shift a_1 0) in
        let r_1 = sin r in
        let r_2 = t_1 (froe321_shift a_1 2) in
        let r_3 = sin r_2 in
        let r_4 = t_1 (froe321_shift a_1 1) in
        let r_5 = sin r_4 in
        let r_6 = cos r in
        let r_7 = cos r_2 in
        let r_8 = cos r_4 in
        let a_2 = froe321_shift a 0 in
        let r_9 = r_1 * r_5 in
        let r_10 = r_6 * r_5 in
        let m =
          froe321_update t_1 (froe321_shift a_2 0) (r_8 * r_7)
        in
        let m_1 =
          froe321_update m (froe321_shift a_2 1) (r_8 * r_3)
        in
        let m_2 =
          froe321_update m_1 (froe321_shift a_2 2) (-r_5)
        in
        let m_3 =
          froe321_update m_2 (froe321_shift a_2 3)
            (r_9 * r_7 + -(r_6 * r_3))
        in
        let m_4 =
          froe321_update m_3 (froe321_shift a_2 4)
            (r_9 * r_3 + r_6 * r_7)
        in
        let m_5 =
          froe321_update m_4 (froe321_shift a_2 5) (r_1 * r_8)
        in
        let m_6 =
          froe321_update m_5 (froe321_shift a_2 6)
            (r_10 * r_7 + r_1 * r_3)
        in
        let m_7 =
          froe321_update m_6 (froe321_shift a_2 7)
            (r_10 * r_3 + -(r_1 * r_7))
        in
        let m_8 =
          froe321_update m_7 (froe321_shift a_2 8) (r_6 * r_8)
        in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          r_1 <= 1 ==>
          r_3 <= 1 ==>
          r_5 <= 1 ==>
          r_6 <= 1 ==>
          r_7 <= 1 ==>
          r_8 <= 1 ==>
          -1 <= r_1 ==>
          -1 <= r_3 ==>
          -1 <= r_5 ==>
          -1 <= r_6 ==>
          -1 <= r_7 ==>
          -1 <= r_8 ==>
          linked t ==>
          froe321_valid_rw t a 9 ==>
          froe321_rvalid_floateulers t t_1 a_1 ==>
          froe321_is_finite32 r ==>
          froe321_is_finite32 r_2 ==>
          froe321_is_finite32 r_4 ==>
          froe321_is_float32 r ==>
          froe321_is_float32 r_2 ==>
          froe321_is_float32 r_4 ==>
          froe321_is_finite32 r_1 ==>
          froe321_is_finite32 r_3 ==>
          froe321_is_finite32 r_5 ==>
          froe321_is_finite32 r_6 ==>
          froe321_is_finite32 r_7 ==>
          froe321_is_finite32 r_8 ==>
          froe321_is_float32 r_1 ==>
          froe321_is_float32 r_3 ==>
          froe321_is_float32 r_5 ==>
          froe321_is_float32 r_6 ==>
          froe321_is_float32 r_7 ==>
          froe321_is_float32 r_8 ==>
          froe321_special_orthogonal (froe321_rmat_of_mem m_8 a)``;

val _ = export_theory();
