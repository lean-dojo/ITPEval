(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_vmult/float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0:
  three sequential memory writes compute a real 3-by-3 matrix-vector product
  from separated readable and writable float regions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0 =
  ``let frvm_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let frvm_update =
      \f : (int # int) -> real. \p : int # int. \v : real.
       \q : int # int.
        if q = p then v else f q
    in
    let frvm_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frvm_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frvm_separated =
      \p : int # int. \n : int. \q : int # int. \m : int.
        n <= 0 \/ m <= 0 \/ FST p <> FST q \/
        SND q + m <= SND p \/ SND p + n <= SND q
    in
    let frvm_is_finite32 = \x : real. T in
    let frvm_is_float32 = \x : real. T in
    let frvm_rvalid_floatvect3 =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        frvm_is_finite32 (mflt (frvm_shift p 0)) /\
        frvm_is_finite32 (mflt (frvm_shift p 1)) /\
        frvm_is_finite32 (mflt (frvm_shift p 2)) /\
        frvm_valid_rd malloc p 3
    in
    let frvm_rvalid_floatrmat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \p : int # int.
        frvm_is_finite32 (mflt (frvm_shift p 0)) /\
        frvm_is_finite32 (mflt (frvm_shift p 1)) /\
        frvm_is_finite32 (mflt (frvm_shift p 2)) /\
        frvm_is_finite32 (mflt (frvm_shift p 3)) /\
        frvm_is_finite32 (mflt (frvm_shift p 4)) /\
        frvm_is_finite32 (mflt (frvm_shift p 5)) /\
        frvm_is_finite32 (mflt (frvm_shift p 6)) /\
        frvm_is_finite32 (mflt (frvm_shift p 7)) /\
        frvm_is_finite32 (mflt (frvm_shift p 8)) /\
        frvm_valid_rd malloc p 9
    in
    let frvm_vect_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (frvm_shift p 0),
         (mflt (frvm_shift p 1), mflt (frvm_shift p 2)))
    in
    let frvm_rmat_of_mem =
      \mflt : (int # int) -> real. \p : int # int.
        (mflt (frvm_shift p 0),
         (mflt (frvm_shift p 1),
          (mflt (frvm_shift p 2),
           (mflt (frvm_shift p 3),
            (mflt (frvm_shift p 4),
             (mflt (frvm_shift p 5),
              (mflt (frvm_shift p 6),
               (mflt (frvm_shift p 7), mflt (frvm_shift p 8)))))))))
    in
    let frvm_m00 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST m
    in
    let frvm_m01 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND m)
    in
    let frvm_m02 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND m))
    in
    let frvm_m10 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND m)))
    in
    let frvm_m11 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND m))))
    in
    let frvm_m12 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND m)))))
    in
    let frvm_m20 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND m))))))
    in
    let frvm_m21 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        FST (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frvm_m22 =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
        SND (SND (SND (SND (SND (SND (SND (SND m)))))))
    in
    let frvm_vx =
      \v : real # (real # real). FST v
    in
    let frvm_vy =
      \v : real # (real # real). FST (SND v)
    in
    let frvm_vz =
      \v : real # (real # real). SND (SND v)
    in
    let frvm_rmat_vmult =
      \m : real # (real # (real # (real # (real # (real #
             (real # (real # real))))))).
       \v : real # (real # real).
        (frvm_m00 m * frvm_vx v +
           frvm_m01 m * frvm_vy v +
           frvm_m02 m * frvm_vz v,
         (frvm_m10 m * frvm_vx v +
            frvm_m11 m * frvm_vy v +
            frvm_m12 m * frvm_vz v,
          frvm_m20 m * frvm_vx v +
            frvm_m21 m * frvm_vy v +
            frvm_m22 m * frvm_vz v))
    in
    let frvm_eq_vect =
      \x y : real # (real # real). y = x
    in
      !a_1 a_2 a : int # int.
      !t_1 : (int # int) -> real.
      !t : int -> int.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        let a_3 = frvm_shift a_1 0 in
        let r = t_1 a_3 in
        let a_4 = frvm_shift a_1 1 in
        let r_1 = t_1 a_4 in
        let a_5 = frvm_shift a_1 2 in
        let r_2 = t_1 a_5 in
        let a_6 = frvm_shift a_2 0 in
        let r_3 = t_1 (frvm_shift a_6 0) in
        let r_4 = t_1 (frvm_shift a_6 1) in
        let r_5 = t_1 (frvm_shift a_6 2) in
        let m =
          frvm_update t_1 (frvm_shift a 0)
            (r_3 * r + r_4 * r_1 + r_5 * r_2)
        in
        let r_6 = m a_3 in
        let r_7 = m a_4 in
        let r_8 = m a_5 in
        let r_9 = m (frvm_shift a_6 3) in
        let r_10 = m (frvm_shift a_6 4) in
        let r_11 = m (frvm_shift a_6 5) in
        let m_1 =
          frvm_update m (frvm_shift a 1)
            (r_9 * r_6 + r_10 * r_7 + r_11 * r_8)
        in
        let r_12 = m_1 a_3 in
        let r_13 = m_1 a_4 in
        let r_14 = m_1 a_5 in
        let r_15 = m_1 (frvm_shift a_6 6) in
        let r_16 = m_1 (frvm_shift a_6 7) in
        let r_17 = m_1 (frvm_shift a_6 8) in
        let m_2 =
          frvm_update m_1 (frvm_shift a 2)
            (r_15 * r_12 + r_16 * r_13 + r_17 * r_14)
        in
          region (FST a) <= 0 ==>
          region (FST a_1) <= 0 ==>
          region (FST a_2) <= 0 ==>
          linked t ==>
          frvm_valid_rw t a 3 ==>
          frvm_rvalid_floatvect3 t t_1 a_1 ==>
          frvm_rvalid_floatrmat t t_1 a_2 ==>
          frvm_separated a 3 a_1 3 ==>
          frvm_separated a 3 a_2 9 ==>
          frvm_separated a_1 3 a_2 9 ==>
          frvm_is_float32 r ==>
          frvm_is_float32 r_1 ==>
          frvm_is_float32 r_2 ==>
          frvm_is_float32 r_3 ==>
          frvm_is_float32 r_4 ==>
          frvm_is_float32 r_5 ==>
          frvm_is_float32 r_6 ==>
          frvm_is_float32 r_7 ==>
          frvm_is_float32 r_8 ==>
          frvm_is_float32 r_9 ==>
          frvm_is_float32 r_10 ==>
          frvm_is_float32 r_11 ==>
          frvm_is_float32 r_12 ==>
          frvm_is_float32 r_13 ==>
          frvm_is_float32 r_14 ==>
          frvm_is_float32 r_15 ==>
          frvm_is_float32 r_16 ==>
          frvm_is_float32 r_17 ==>
          frvm_eq_vect
            (frvm_vect_of_mem m_2 a)
            (frvm_rmat_vmult
              (frvm_rmat_of_mem m_2 a_2)
              (frvm_vect_of_mem m_2 a_1))``;
