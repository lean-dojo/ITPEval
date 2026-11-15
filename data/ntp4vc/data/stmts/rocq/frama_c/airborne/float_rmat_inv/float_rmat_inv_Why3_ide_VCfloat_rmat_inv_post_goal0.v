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
Require Import float_rmat_inv.Axiomatic15.Axiomatic15.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_inv.Compound.Compound.
Require Import float_rmat_inv.S10_RealRMat_s.S10_RealRMat_s.
Require Import float_rmat_inv.Axiomatic17.Axiomatic17.
Open Scope Z_scope.
Theorem goal0 (a : addr) (a_1 : addr) (t_1 : addr -> R) (t : Z -> Z) : let a_2 : addr := shift a 0%Z in let a_3 : addr := shift a_1 0%Z in let m : addr -> R := fun_updt t_1 (shift a_2 0%Z) (t_1 (shift a_3 0%Z)) in let m_1 : addr -> R := fun_updt m (shift a_2 1%Z) (m (shift a_3 3%Z)) in let m_2 : addr -> R := fun_updt m_1 (shift a_2 2%Z) (m_1 (shift a_3 6%Z)) in let m_3 : addr -> R := fun_updt m_2 (shift a_2 3%Z) (m_2 (shift a_3 1%Z)) in let m_4 : addr -> R := fun_updt m_3 (shift a_2 4%Z) (m_3 (shift a_3 4%Z)) in let m_5 : addr -> R := fun_updt m_4 (shift a_2 5%Z) (m_4 (shift a_3 7%Z)) in let m_6 : addr -> R := fun_updt m_5 (shift a_2 6%Z) (m_5 (shift a_3 2%Z)) in let m_7 : addr -> R := fun_updt m_6 (shift a_2 7%Z) (m_6 (shift a_3 5%Z)) in let m_8 : addr -> R := fun_updt m_7 (shift a_2 8%Z) (m_7 (shift a_3 8%Z)) in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> valid_rw t a 9%Z -> p_rvalid_floatrmat t t_1 a_1 -> separated a 9%Z a_1 9%Z -> eqs10_realrmat_s (l_transpose (l_l_rmat_of_floatrmat m_8 a_1)) (l_l_rmat_of_floatrmat m_8 a).
Admitted.
