(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_transp_vmult/float_rmat_transp_vmult_Why3_ide_VCfloat_rmat_transp_vmult_post_goal0:
  three sequential memory writes compute a transposed real 3-by-3 matrix-vector
  product from separated readable and writable float regions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_rmat_transp_vmult_Why3_ide_VCfloat_rmat_transp_vmult_post_goal0 =
  ``let frtv_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let frtv_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let frtv_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frtv_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frtv_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let frtv_is_finite32 = \x : real. T in
    let frtv_is_float32 = \x : real. T in
    let frtv_rvalid_floatvect3 =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        frtv_is_finite32 (mflt (frtv_shift p 0)) /\
        frtv_is_finite32 (mflt (frtv_shift p 1)) /\
        frtv_is_finite32 (mflt (frtv_shift p 2)) /\
        frtv_valid_rd malloc p 3
    in
    let frtv_rvalid_floatrmat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        frtv_is_finite32 (mflt (frtv_shift p 0)) /\
        frtv_is_finite32 (mflt (frtv_shift p 1)) /\
        frtv_is_finite32 (mflt (frtv_shift p 2)) /\
        frtv_is_finite32 (mflt (frtv_shift p 3)) /\
        frtv_is_finite32 (mflt (frtv_shift p 4)) /\
        frtv_is_finite32 (mflt (frtv_shift p 5)) /\
        frtv_is_finite32 (mflt (frtv_shift p 6)) /\
        frtv_is_finite32 (mflt (frtv_shift p 7)) /\
        frtv_is_finite32 (mflt (frtv_shift p 8)) /\
        frtv_valid_rd malloc p 9
    in
    let frtv_vect_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (frtv_shift p 0),
         (mflt (frtv_shift p 1), mflt (frtv_shift p 2)))
    in
    let frtv_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (frtv_shift p 0),
         (mflt (frtv_shift p 1),
          (mflt (frtv_shift p 2),
           (mflt (frtv_shift p 3),
            (mflt (frtv_shift p 4),
             (mflt (frtv_shift p 5),
              (mflt (frtv_shift p 6),
               (mflt (frtv_shift p 7), mflt (frtv_shift p 8)))))))))
    in
    let frtv_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let frtv_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let frtv_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let frtv_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let frtv_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let frtv_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let frtv_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let frtv_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frtv_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frtv_transpose =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        (frtv_m00 m,
         (frtv_m10 m,
          (frtv_m20 m,
           (frtv_m01 m,
            (frtv_m11 m,
             (frtv_m21 m,
              (frtv_m02 m, (frtv_m12 m, frtv_m22 m))))))))
    in
    let frtv_vx =
      \v : real # (real # real). FST v
    in
    let frtv_vy =
      \v : real # (real # real). FST (SND v)
    in
    let frtv_vz =
      \v : real # (real # real). SND (SND v)
    in
    let frtv_rmat_vmult =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
       \v : real # (real # real).
        (frtv_m00 m * frtv_vx v +
           frtv_m01 m * frtv_vy v +
           frtv_m02 m * frtv_vz v,
         (frtv_m10 m * frtv_vx v +
            frtv_m11 m * frtv_vy v +
            frtv_m12 m * frtv_vz v,
          frtv_m20 m * frtv_vx v +
            frtv_m21 m * frtv_vy v +
            frtv_m22 m * frtv_vz v))
    in
    let frtv_eq_vect =
      \x y : real # (real # real). y = x
    in
      !a_1 a_2 a : int # int.
      !t_1 : (int # int) -> real.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_3 = frtv_shift a_1 0 in
        let r = t_1 a_3 in
        let a_4 = frtv_shift a_1 1 in
        let r_1 = t_1 a_4 in
        let a_5 = frtv_shift a_1 2 in
        let r_2 = t_1 a_5 in
        let a_6 = frtv_shift a_2 0 in
        let r_3 = t_1 (frtv_shift a_6 0) in
        let r_4 = t_1 (frtv_shift a_6 3) in
        let r_5 = t_1 (frtv_shift a_6 6) in
        let m =
          frtv_update t_1 (frtv_shift a 0)
            (r_3 * r + r_4 * r_1 + r_5 * r_2)
        in
        let r_6 = m a_3 in
        let r_7 = m a_4 in
        let r_8 = m a_5 in
        let r_9 = m (frtv_shift a_6 1) in
        let r_10 = m (frtv_shift a_6 4) in
        let r_11 = m (frtv_shift a_6 7) in
        let m_1 =
          frtv_update m (frtv_shift a 1)
            (r_9 * r_6 + r_10 * r_7 + r_11 * r_8)
        in
        let r_12 = m_1 a_3 in
        let r_13 = m_1 a_4 in
        let r_14 = m_1 a_5 in
        let r_15 = m_1 (frtv_shift a_6 2) in
        let r_16 = m_1 (frtv_shift a_6 5) in
        let r_17 = m_1 (frtv_shift a_6 8) in
        let m_2 =
          frtv_update m_1 (frtv_shift a 2)
            (r_15 * r_12 + r_16 * r_13 + r_17 * r_14)
        in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          linked t ==>
          frtv_valid_rw t a 3 ==>
          frtv_rvalid_floatvect3 t t_1 a_1 ==>
          frtv_rvalid_floatrmat t t_1 a_2 ==>
          frtv_separated a 3 a_1 3 ==>
          frtv_separated a 3 a_2 9 ==>
          frtv_separated a_1 3 a_2 9 ==>
          frtv_is_float32 r ==>
          frtv_is_float32 r_1 ==>
          frtv_is_float32 r_2 ==>
          frtv_is_float32 r_3 ==>
          frtv_is_float32 r_4 ==>
          frtv_is_float32 r_5 ==>
          frtv_is_float32 r_6 ==>
          frtv_is_float32 r_7 ==>
          frtv_is_float32 r_8 ==>
          frtv_is_float32 r_9 ==>
          frtv_is_float32 r_10 ==>
          frtv_is_float32 r_11 ==>
          frtv_is_float32 r_12 ==>
          frtv_is_float32 r_13 ==>
          frtv_is_float32 r_14 ==>
          frtv_is_float32 r_15 ==>
          frtv_is_float32 r_16 ==>
          frtv_is_float32 r_17 ==>
          frtv_eq_vect
            (frtv_vect_of_mem m_2 a)
            (frtv_rmat_vmult
              (frtv_transpose (frtv_rmat_of_mem m_2 a_2))
              (frtv_vect_of_mem m_2 a_1))``;
