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
Open Scope Z_scope.
Theorem goal6 (a : addr) (t_1 : addr -> R) (a_1 : addr) (t : Z -> Z) : let a_2 : addr := shift a 0%Z in let r : R := t_1 (shift a_2 8%Z) in let r_1 : R := t_1 (shift a_2 4%Z) in let r_2 : R := t_1 (shift a_2 0%Z) in let r_3 : R := Rplus (Rplus r_2 r_1) r in let a_3 : s10_realrmat_s := l_l_rmat_of_floatrmat t_1 a in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> Rlt r r_1 -> Rle r_3 0%R -> linked t -> valid_rw t a_1 4%Z -> p_rvalid_floatrmat t t_1 a -> separated a 9%Z a_1 4%Z -> p_rotation_matrix a_3 -> p_special_orthogonal a_3 -> is_float32 r_2 -> is_float32 (t_1 (shift a_2 2%Z)) -> is_float32 r_1 -> is_float32 (t_1 (shift a_2 6%Z)) -> is_float32 r -> is_float32 r_3 -> Rle r_2 r_1 ∨ Rle r_2 r -> Rle 0%R (Rplus (Rplus (Rplus r_1 (Ropp r_2)) (Ropp r)) 1%R).
Admitted.
