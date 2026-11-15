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
Require Import float_quat_comp.Compound.Compound.
Require Import float_quat_comp.Axiomatic15.Axiomatic15.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_quat_comp.S12_RealQuatVect_s.S12_RealQuatVect_s.
Require Import float_quat_comp.S9_RealVect3_s.S9_RealVect3_s.
Require Import float_quat_comp.Axiomatic19.Axiomatic19.
Require Import float_quat_comp.Axiomatic16.Axiomatic16.
Open Scope Z_scope.
Theorem goal0 (a_1 : addr) (a : addr) (a_2 : addr) (t_1 : addr -> R) (t : Z -> Z) : let a_3 : addr := shift a_1 0%Z in let a_4 : addr := shift a 0%Z in let a_5 : addr := shift a_2 0%Z in let a_6 : addr := shift a 1%Z in let a_7 : addr := shift a_1 1%Z in let a_8 : addr := shift a_2 1%Z in let a_9 : addr := shift a 2%Z in let a_10 : addr := shift a_1 2%Z in let a_11 : addr := shift a_2 2%Z in let a_12 : addr := shift a 3%Z in let a_13 : addr := shift a_1 3%Z in let a_14 : addr := shift a_2 3%Z in let r : R := t_1 a_4 in let r_1 : R := t_1 a_5 in let r_2 : R := t_1 a_6 in let r_3 : R := t_1 a_8 in let r_4 : R := t_1 a_9 in let r_5 : R := t_1 a_11 in let r_6 : R := t_1 a_12 in let r_7 : R := t_1 a_14 in let m : addr -> R := fun_updt t_1 a_3 (Rplus (Rplus (Rplus (Rmult r_1 r) (Ropp (Rmult r_3 r_2))) (Ropp (Rmult r_5 r_4))) (Ropp (Rmult r_7 r_6))) in let r_8 : R := m a_4 in let r_9 : R := m a_5 in let r_10 : R := m a_6 in let r_11 : R := m a_8 in let r_12 : R := m a_9 in let r_13 : R := m a_11 in let r_14 : R := m a_12 in let r_15 : R := m a_14 in let m_1 : addr -> R := fun_updt m a_7 (Rplus (Rplus (Rplus (Rmult r_9 r_10) (Rmult r_11 r_8)) (Rmult r_13 r_14)) (Ropp (Rmult r_15 r_12))) in let r_16 : R := m_1 a_4 in let r_17 : R := m_1 a_5 in let r_18 : R := m_1 a_6 in let r_19 : R := m_1 a_8 in let r_20 : R := m_1 a_9 in let r_21 : R := m_1 a_11 in let r_22 : R := m_1 a_12 in let r_23 : R := m_1 a_14 in let m_2 : addr -> R := fun_updt m_1 a_10 (Rplus (Rplus (Rplus (Rmult r_17 r_20) (Ropp (Rmult r_19 r_22))) (Rmult r_21 r_16)) (Rmult r_23 r_18)) in let r_24 : R := m_2 a_4 in let r_25 : R := m_2 a_5 in let r_26 : R := m_2 a_6 in let r_27 : R := m_2 a_8 in let r_28 : R := m_2 a_9 in let r_29 : R := m_2 a_11 in let r_30 : R := m_2 a_12 in let r_31 : R := m_2 a_14 in let m_3 : addr -> R := fun_updt m_2 a_13 (Rplus (Rplus (Rplus (Rmult r_25 r_30) (Rmult r_27 r_28)) (Ropp (Rmult r_29 r_26))) (Rmult r_31 r_24)) in ¬ a_3 = a_4 -> ¬ a_5 = a_4 -> ¬ a_5 = a_3 -> ¬ a_6 = a_3 -> ¬ a_6 = a_5 -> ¬ a_7 = a_4 -> ¬ a_7 = a_5 -> ¬ a_7 = a_6 -> ¬ a_8 = a_4 -> ¬ a_8 = a_3 -> ¬ a_8 = a_6 -> ¬ a_8 = a_7 -> ¬ a_9 = a_3 -> ¬ a_9 = a_5 -> ¬ a_9 = a_7 -> ¬ a_9 = a_8 -> ¬ a_10 = a_4 -> ¬ a_10 = a_5 -> ¬ a_10 = a_6 -> ¬ a_10 = a_8 -> ¬ a_10 = a_9 -> ¬ a_11 = a_4 -> ¬ a_11 = a_3 -> ¬ a_11 = a_6 -> ¬ a_11 = a_7 -> ¬ a_11 = a_9 -> ¬ a_11 = a_10 -> ¬ a_12 = a_3 -> ¬ a_12 = a_5 -> ¬ a_12 = a_7 -> ¬ a_12 = a_8 -> ¬ a_12 = a_10 -> ¬ a_12 = a_11 -> ¬ a_13 = a_4 -> ¬ a_13 = a_5 -> ¬ a_13 = a_6 -> ¬ a_13 = a_8 -> ¬ a_13 = a_9 -> ¬ a_13 = a_11 -> ¬ a_13 = a_12 -> ¬ a_14 = a_4 -> ¬ a_14 = a_3 -> ¬ a_14 = a_6 -> ¬ a_14 = a_7 -> ¬ a_14 = a_9 -> ¬ a_14 = a_10 -> ¬ a_14 = a_12 -> ¬ a_14 = a_13 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> linked t -> valid_rw t a_1 4%Z -> p_rvalid_floatquat t t_1 a -> p_rvalid_floatquat t t_1 a_2 -> is_float32 r -> is_float32 r_1 -> is_float32 r_2 -> is_float32 r_3 -> is_float32 r_4 -> is_float32 r_5 -> is_float32 r_6 -> is_float32 r_7 -> is_float32 r_8 -> is_float32 r_9 -> is_float32 r_10 -> is_float32 r_11 -> is_float32 r_12 -> is_float32 r_13 -> is_float32 r_14 -> is_float32 r_15 -> is_float32 r_16 -> is_float32 r_17 -> is_float32 r_18 -> is_float32 r_19 -> is_float32 r_20 -> is_float32 r_21 -> is_float32 r_22 -> is_float32 r_23 -> is_float32 r_24 -> is_float32 r_25 -> is_float32 r_26 -> is_float32 r_27 -> is_float32 r_28 -> is_float32 r_29 -> is_float32 r_30 -> is_float32 r_31 -> eqs12_realquatvect_s (l_l_quatvect_of_floatquat m_3 a_1) (l_mult_realquatvect (l_l_quatvect_of_floatquat m_3 a_2) (l_l_quatvect_of_floatquat m_3 a)).
Admitted.
