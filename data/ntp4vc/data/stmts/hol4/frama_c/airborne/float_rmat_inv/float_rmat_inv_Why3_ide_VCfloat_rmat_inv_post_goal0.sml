(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_inv/float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0:
  nine functional memory updates copy a readable real 3-by-3 float matrix
  into separated writable storage in transposed order. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0 =
  ``let frmi_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let frmi_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let frmi_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frmi_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frmi_separated =
      \p : int # int. \a : int. \q : int # int. \b : int.
        a <= 0 \/ b <= 0 \/ FST p <> FST q \/
        SND q + b <= SND p \/ SND p + a <= SND q
    in
    let frmi_is_finite32 = \x : real. T in
    let frmi_rvalid_floatrmat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        frmi_is_finite32 (mflt (frmi_shift p 0)) /\
        frmi_is_finite32 (mflt (frmi_shift p 1)) /\
        frmi_is_finite32 (mflt (frmi_shift p 2)) /\
        frmi_is_finite32 (mflt (frmi_shift p 3)) /\
        frmi_is_finite32 (mflt (frmi_shift p 4)) /\
        frmi_is_finite32 (mflt (frmi_shift p 5)) /\
        frmi_is_finite32 (mflt (frmi_shift p 6)) /\
        frmi_is_finite32 (mflt (frmi_shift p 7)) /\
        frmi_is_finite32 (mflt (frmi_shift p 8)) /\
        frmi_valid_rd malloc p 9
    in
    let frmi_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (frmi_shift p 0),
         (mflt (frmi_shift p 1),
          (mflt (frmi_shift p 2),
           (mflt (frmi_shift p 3),
            (mflt (frmi_shift p 4),
             (mflt (frmi_shift p 5),
              (mflt (frmi_shift p 6),
               (mflt (frmi_shift p 7), mflt (frmi_shift p 8)))))))))
    in
    let frmi_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let frmi_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let frmi_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let frmi_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let frmi_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let frmi_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let frmi_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let frmi_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frmi_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frmi_transpose =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        (frmi_m00 m,
         (frmi_m10 m,
          (frmi_m20 m,
           (frmi_m01 m,
            (frmi_m11 m,
             (frmi_m21 m,
              (frmi_m02 m, (frmi_m12 m, frmi_m22 m))))))))
    in
    let frmi_eq_rmat =
      \x y : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        y = x
    in
      !a a_1 : int # int.
      !t_1 : (int # int) -> real.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_2 = frmi_shift a 0 in
        let a_3 = frmi_shift a_1 0 in
        let m =
          frmi_update t_1 (frmi_shift a_2 0)
            (t_1 (frmi_shift a_3 0))
        in
        let m_1 =
          frmi_update m (frmi_shift a_2 1)
            (m (frmi_shift a_3 3))
        in
        let m_2 =
          frmi_update m_1 (frmi_shift a_2 2)
            (m_1 (frmi_shift a_3 6))
        in
        let m_3 =
          frmi_update m_2 (frmi_shift a_2 3)
            (m_2 (frmi_shift a_3 1))
        in
        let m_4 =
          frmi_update m_3 (frmi_shift a_2 4)
            (m_3 (frmi_shift a_3 4))
        in
        let m_5 =
          frmi_update m_4 (frmi_shift a_2 5)
            (m_4 (frmi_shift a_3 7))
        in
        let m_6 =
          frmi_update m_5 (frmi_shift a_2 6)
            (m_5 (frmi_shift a_3 2))
        in
        let m_7 =
          frmi_update m_6 (frmi_shift a_2 7)
            (m_6 (frmi_shift a_3 5))
        in
        let m_8 =
          frmi_update m_7 (frmi_shift a_2 8)
            (m_7 (frmi_shift a_3 8))
        in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          linked t ==>
          frmi_valid_rw t a 9 ==>
          frmi_rvalid_floatrmat t t_1 a_1 ==>
          frmi_separated a 9 a_1 9 ==>
          frmi_eq_rmat
            (frmi_transpose (frmi_rmat_of_mem m_8 a_1))
            (frmi_rmat_of_mem m_8 a)``;
