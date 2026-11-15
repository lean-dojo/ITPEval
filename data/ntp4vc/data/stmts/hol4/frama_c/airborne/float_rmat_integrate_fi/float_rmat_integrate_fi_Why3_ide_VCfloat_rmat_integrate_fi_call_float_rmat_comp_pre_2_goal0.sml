(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_integrate_fi/float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0:
  validity of a writable nine-entry real matrix region under the floating-point
  rate-input and memory assumptions. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory realTheory;

val float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0 =
  ``let frifi_shift =
      \p : int # int. \k : int. (FST p, SND p + k)
    in
    let frifi_valid_rw =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        0 < FST p /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frifi_valid_rd =
      \malloc : int -> int. \p : int # int. \n : int.
        0 < n ==>
        FST p <> 0 /\ 0 <= SND p /\ SND p + n <= malloc (FST p)
    in
    let frifi_is_float32 = \x : real. T in
    let frifi_is_finite32 = \x : real. T in
    let frifi_rvalid_floatrates =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \r : int # int.
        frifi_is_finite32 (mflt (frifi_shift r 0)) /\
        frifi_is_finite32 (mflt (frifi_shift r 1)) /\
        frifi_is_finite32 (mflt (frifi_shift r 2)) /\
        frifi_valid_rd malloc r 3
    in
    let frifi_rvalid_floatrmat =
      \malloc : int -> int. \mflt : (int # int) -> real.
       \rm : int # int.
        frifi_is_finite32 (mflt (frifi_shift rm 0)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 1)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 2)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 3)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 4)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 5)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 6)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 7)) /\
        frifi_is_finite32 (mflt (frifi_shift rm 8)) /\
        frifi_valid_rd malloc rm 9
    in
      !a a_1 : int # int.
      !t : int -> int.
      !t_1 : (int # int) -> real.
      !region : int -> int.
      !linked : (int -> int) -> bool.
        region (FST a) <= 0 ==>
        region (FST a_1) <= 0 ==>
        linked t ==>
        frifi_valid_rw t a 9 ==>
        frifi_rvalid_floatrates t t_1 a_1 ==>
        frifi_is_float32 (t_1 (frifi_shift a_1 0)) ==>
        frifi_is_float32 (t_1 (frifi_shift a_1 1)) ==>
        frifi_is_float32 (t_1 (frifi_shift a_1 2)) ==>
        frifi_rvalid_floatrmat t t_1 a``;
