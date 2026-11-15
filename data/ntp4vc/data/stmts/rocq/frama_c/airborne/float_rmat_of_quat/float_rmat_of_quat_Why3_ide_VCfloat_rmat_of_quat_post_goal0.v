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
Require Import float_rmat_of_quat.Axiomatic19.Axiomatic19.
Require Import float_rmat_of_quat.S10_RealRMat_s.S10_RealRMat_s.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_of_quat.Compound.Compound.
Require Import float_rmat_of_quat.Axiomatic15.Axiomatic15.
Require Import float_rmat_of_quat.Axiomatic17.Axiomatic17.
Open Scope Z_scope.
Theorem goal0 (t_1 : addr -> R) (a_1 : addr) (a : addr) (t : Z -> Z) : let r : R := t_1 (shift a_1 0%Z) in let r_1 : R := t_1 (shift a_1 1%Z) in let r_2 : R := t_1 (shift a_1 2%Z) in let r_3 : R := t_1 (shift a_1 3%Z) in let r_4 : R := Rmult 2%R r in let r_5 : R := Rmult 2%R r_1 in let r_6 : R := Rmult 2%R r_3 in let r_7 : R := Rmult r_4 r_1 in let r_8 : R := Rmult r_4 r_2 in let r_9 : R := Rmult r_4 r_3 in let r_10 : R := Rmult r_5 r_2 in let r_11 : R := Rmult r_5 r_3 in let r_12 : R := Rmult r_2 r_6 in let r_13 : R := Rplus (Rmult r_4 r) (Ropp 1%R) in let a_2 : addr := shift a 0%Z in let m : addr -> R := fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt t_1 (shift a_2 0%Z) (Rplus r_13 (Rmult r_5 r_1))) (shift a_2 1%Z) (Rplus r_10 r_9)) (shift a_2 2%Z) (Rplus r_11 (Ropp r_8))) (shift a_2 3%Z) (Rplus r_10 (Ropp r_9))) (shift a_2 4%Z) (Rplus r_13 (Rmult (Rmult 2%R r_2) r_2))) (shift a_2 5%Z) (Rplus r_12 r_7)) (shift a_2 6%Z) (Rplus r_11 r_8)) (shift a_2 7%Z) (Rplus r_12 (Ropp r_7))) (shift a_2 8%Z) (Rplus r_13 (Rmult r_6 r_3)) in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> p_unitary_quaternion_1' t_1 a_1 -> valid_rw t a 9%Z -> p_rvalid_floatquat t t_1 a_1 -> separated a 9%Z a_1 4%Z -> is_float32 r -> is_float32 r_1 -> is_float32 r_2 -> is_float32 r_3 -> is_float32 r_4 -> is_float32 r_5 -> is_float32 r_6 -> is_float32 r_7 -> is_float32 r_8 -> is_float32 r_9 -> is_float32 r_10 -> is_float32 r_11 -> is_float32 r_12 -> is_float32 r_13 -> eqs10_realrmat_s (l_transpose (l_l_rmat_of_floatrmat m a)) (l_l_rmat_of_floatquat_1' m a_1).
Admitted.
