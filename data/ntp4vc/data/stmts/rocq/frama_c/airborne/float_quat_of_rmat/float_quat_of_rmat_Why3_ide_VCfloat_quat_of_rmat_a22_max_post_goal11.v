From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.Qed.Qed.
Require Import Why3.Memory.Memory.
Require Import float_quat_of_rmat.Axiomatic15.Axiomatic15.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_quat_of_rmat.Compound.Compound.
Require Import float_quat_of_rmat.Axiomatic17.Axiomatic17.
Require Import float_quat_of_rmat.S10_RealRMat_s.S10_RealRMat_s.
Require Import float_quat_of_rmat.Axiomatic19.Axiomatic19.
Require Import float_quat_of_rmat.S11_RealQuat_s.S11_RealQuat_s.
Require Import Why3.Square.Square.
Require Import float_quat_of_rmat.Axiomatic18.Axiomatic18.
Open Scope Z_scope.
Theorem goal11 (a : addr) (t_1 : addr -> R) (a_1 : addr) (t_8 : addr -> R) (r_3 : R) (r_7 : R) (t_7 : addr -> R) (r_6 : R) (r_2 : R) (t_4 : addr -> R) (r_1 : R) (t_6 : addr -> R) (r_5 : R) (r : R) (t_5 : addr -> R) (r_4 : R) (t : Z -> Z) (t_9 : addr -> R) (t_2 : addr -> R) (t_3 : addr -> R) : let a_2 : addr := shift a 0%Z in let a_3 : addr := shift a_2 0%Z in let r_8 : R := t_1 a_3 in let a_4 : addr := shift a_2 8%Z in let r_9 : R := t_1 a_4 in let a_5 : addr := shift a_2 4%Z in let r_10 : R := t_1 a_5 in let a_6 : s10_realrmat_s := l_l_rmat_of_floatrmat t_1 a in let r_11 : R := Rplus (Rplus r_8 r_10) r_9 in let a_7 : addr := shift a_1 0%Z in let m : addr -> R := fun_updt t_8 a_7 (Rmult (Rdiv 1%R 2%R) r_3) in let a_8 : addr := shift a_1 1%Z in let a_9 : addr := shift a_2 5%Z in let a_10 : addr := shift a_2 7%Z in let m_1 : addr -> R := fun_updt m a_8 (Rdiv (Rplus (m a_9) (Ropp (m a_10))) r_7) in let a_11 : addr := shift a_1 2%Z in let a_12 : addr := shift a_2 6%Z in let a_13 : addr := shift a_2 2%Z in let m_2 : addr -> R := fun_updt m_1 a_11 (Rdiv (Rplus (m_1 a_12) (Ropp (m_1 a_13))) r_7) in let a_14 : addr := shift a_1 3%Z in let a_15 : addr := shift a_2 1%Z in let a_16 : addr := shift a_2 3%Z in let r_13 : R := Rplus 1%R (Rplus (Rplus (t_8 a_3) (t_8 a_5)) (t_8 a_4)) in let m_3 : addr -> R := fun_updt (fun_updt t_7 a_7 (Rdiv (Rplus (t_7 a_9) (Ropp (t_7 a_10))) r_6)) a_8 (Rmult (Rdiv 1%R 2%R) r_2) in let m_4 : addr -> R := fun_updt m_3 a_11 (Rdiv (Rplus (m_3 a_15) (m_3 a_16)) r_6) in let r_15 : R := Rplus (Rplus (Rplus (t_7 a_3) (Ropp (t_7 a_5))) (Ropp (t_7 a_4))) 1%R in let r_16 : R := t_4 a_4 in let r_17 : R := t_4 a_5 in let r_19 : R := Rmult 2%R r_1 in let m_5 : addr -> R := fun_updt t_6 a_7 (Rdiv (Rplus (t_6 a_12) (Ropp (t_6 a_13))) r_5) in let m_6 : addr -> R := fun_updt (fun_updt m_5 a_8 (Rdiv (Rplus (m_5 a_15) (m_5 a_16)) r_5)) a_11 (Rmult (Rdiv 1%R 2%R) r_1) in let m_7 : addr -> R := fun_updt m_6 a_14 (Rdiv (Rplus (m_6 a_9) (m_6 a_10)) r_5) in let r_20 : R := Rplus (Rplus (Rplus (t_6 a_5) (Ropp (t_6 a_3))) (Ropp (t_6 a_4))) 1%R in let r_22 : R := Rmult 2%R r in let m_8 : addr -> R := fun_updt t_5 a_7 (Rdiv (Rplus (t_5 a_15) (Ropp (t_5 a_16))) r_4) in let m_9 : addr -> R := fun_updt m_8 a_8 (Rdiv (Rplus (m_8 a_12) (m_8 a_13)) r_4) in let m_10 : addr -> R := fun_updt (fun_updt m_9 a_11 (Rdiv (Rplus (m_9 a_9) (m_9 a_10)) r_4)) a_14 (Rmult (Rdiv 1%R 2%R) r) in let r_23 : R := Rplus (Rplus (Rplus (t_5 a_4) (Ropp (t_5 a_3))) (Ropp (t_5 a_5))) 1%R in Rle (l_trace_2' t_1 a) 0%R -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> Rle r_8 r_9 -> Rle r_10 r_9 -> linked t -> is_float32 r -> is_float32 r_1 -> is_float32 r_2 -> is_float32 r_3 -> is_float32 r_4 -> is_float32 r_5 -> is_float32 r_6 -> is_float32 r_7 -> valid_rw t a_1 4%Z -> p_rvalid_floatrmat t t_1 a -> separated a 9%Z a_1 4%Z -> p_rotation_matrix a_6 -> p_special_orthogonal a_6 -> is_float32 r_8 -> is_float32 r_10 -> is_float32 r_9 -> is_float32 r_11 -> (if decide (Rlt 0%R r_11) then t_8 = t_1 ∧ Rmult 2%R r_3 = r_7 ∧ fun_updt m_2 a_14 (Rdiv (Rplus (m_2 a_15) (Ropp (m_2 a_16))) r_7) = t_9 ∧ Rle 0%R r_3 ∧ Rle 0%R r_13 ∧ is_finite32 r_3 ∧ is_finite32 r_13 else t_2 = t_1 ∧ (if decide (Rlt (t_2 a_5) (t_2 a_3)) then t_3 = t_2 ∧ (if decide (Rlt (t_3 a_4) (t_3 a_3)) then t_7 = t_3 ∧ Rmult 2%R r_2 = r_6 ∧ fun_updt m_4 a_14 (Rdiv (Rplus (m_4 a_12) (m_4 a_13)) r_6) = t_9 ∧ Rle 0%R r_2 ∧ Rle 0%R r_15 ∧ is_finite32 r_2 ∧ is_finite32 r_15 else t_4 = t_3 ∧ (if decide (Rlt r_16 r_17) then t_6 = t_4 ∧ r_19 = r_5 ∧ m_7 = t_9 ∧ Rle 0%R r_1 ∧ Rle 0%R r_20 ∧ is_finite32 r_1 ∧ is_finite32 r_20 else t_5 = t_4 ∧ r_22 = r_4 ∧ m_10 = t_9 ∧ Rle 0%R r ∧ Rle 0%R r_23 ∧ is_finite32 r ∧ is_finite32 r_23)) else t_4 = t_2 ∧ (if decide (Rlt r_16 r_17) then t_6 = t_4 ∧ r_19 = r_5 ∧ m_7 = t_9 ∧ Rle 0%R r_1 ∧ Rle 0%R r_20 ∧ is_finite32 r_1 ∧ is_finite32 r_20 else t_5 = t_4 ∧ r_22 = r_4 ∧ m_10 = t_9 ∧ Rle 0%R r ∧ Rle 0%R r_23 ∧ is_finite32 r ∧ is_finite32 r_23))) -> eqs11_realquat_s (l_l_floatquat_of_rmat_2_max_t t_9 a) (l_l_quat_of_floatquat t_9 a_1).
Admitted.
