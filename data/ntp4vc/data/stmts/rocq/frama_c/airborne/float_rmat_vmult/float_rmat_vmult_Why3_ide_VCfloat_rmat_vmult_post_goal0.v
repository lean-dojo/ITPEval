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
Require Import float_rmat_vmult.Axiomatic15.Axiomatic15.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_vmult.Compound.Compound.
Require Import float_rmat_vmult.S9_RealVect3_s.S9_RealVect3_s.
Require Import float_rmat_vmult.Axiomatic16.Axiomatic16.
Require Import float_rmat_vmult.Axiomatic17.Axiomatic17.
Require Import float_rmat_vmult.S10_RealRMat_s.S10_RealRMat_s.
Open Scope Z_scope.
Theorem goal0 (a_1 : addr) (t_1 : addr -> R) (a_2 : addr) (a : addr) (t : Z -> Z) : let a_3 : addr := shift a_1 0%Z in let r : R := t_1 a_3 in let a_4 : addr := shift a_1 1%Z in let r_1 : R := t_1 a_4 in let a_5 : addr := shift a_1 2%Z in let r_2 : R := t_1 a_5 in let a_6 : addr := shift a_2 0%Z in let r_3 : R := t_1 (shift a_6 0%Z) in let r_4 : R := t_1 (shift a_6 1%Z) in let r_5 : R := t_1 (shift a_6 2%Z) in let m : addr -> R := fun_updt t_1 (shift a 0%Z) (Rplus (Rplus (Rmult r_3 r) (Rmult r_4 r_1)) (Rmult r_5 r_2)) in let r_6 : R := m a_3 in let r_7 : R := m a_4 in let r_8 : R := m a_5 in let r_9 : R := m (shift a_6 3%Z) in let r_10 : R := m (shift a_6 4%Z) in let r_11 : R := m (shift a_6 5%Z) in let m_1 : addr -> R := fun_updt m (shift a 1%Z) (Rplus (Rplus (Rmult r_9 r_6) (Rmult r_10 r_7)) (Rmult r_11 r_8)) in let r_12 : R := m_1 a_3 in let r_13 : R := m_1 a_4 in let r_14 : R := m_1 a_5 in let r_15 : R := m_1 (shift a_6 6%Z) in let r_16 : R := m_1 (shift a_6 7%Z) in let r_17 : R := m_1 (shift a_6 8%Z) in let m_2 : addr -> R := fun_updt m_1 (shift a 2%Z) (Rplus (Rplus (Rmult r_15 r_12) (Rmult r_16 r_13)) (Rmult r_17 r_14)) in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> linked t -> valid_rw t a 3%Z -> p_rvalid_floatvect3 t t_1 a_1 -> p_rvalid_floatrmat t t_1 a_2 -> separated a 3%Z a_1 3%Z -> separated a 3%Z a_2 9%Z -> separated a_1 3%Z a_2 9%Z -> is_float32 r -> is_float32 r_1 -> is_float32 r_2 -> is_float32 r_3 -> is_float32 r_4 -> is_float32 r_5 -> is_float32 r_6 -> is_float32 r_7 -> is_float32 r_8 -> is_float32 r_9 -> is_float32 r_10 -> is_float32 r_11 -> is_float32 r_12 -> is_float32 r_13 -> is_float32 r_14 -> is_float32 r_15 -> is_float32 r_16 -> is_float32 r_17 -> eqs9_realvect3_s (l_l_vect_of_floatvect3 m_2 a) (l_mult_realrmat_realvect3 (l_l_rmat_of_floatrmat m_2 a_2) (l_l_vect_of_floatvect3 m_2 a_1)).
Admitted.
