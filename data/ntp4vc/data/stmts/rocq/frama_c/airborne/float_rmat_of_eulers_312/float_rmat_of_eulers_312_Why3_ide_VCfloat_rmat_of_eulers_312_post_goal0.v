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
Require Import Why3.Cmath.Cmath.
Require Import Why3.Square.Square.
Require Import float_rmat_of_eulers_312.Compound.Compound.
Require Import float_rmat_of_eulers_312.Axiomatic15.Axiomatic15.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_of_eulers_312.Axiomatic17.Axiomatic17.
Require Import float_rmat_of_eulers_312.S10_RealRMat_s.S10_RealRMat_s.
Open Scope Z_scope.
Theorem goal0 (t_1 : addr -> R) (a_1 : addr) (a : addr) (t : Z -> Z) : let r : R := t_1 (shift a_1 0%Z) in let r_1 : R := sin r in let r_2 : R := t_1 (shift a_1 2%Z) in let r_3 : R := sin r_2 in let r_4 : R := t_1 (shift a_1 1%Z) in let r_5 : R := sin r_4 in let r_6 : R := cos r in let r_7 : R := cos r_2 in let r_8 : R := cos r_4 in let a_2 : addr := shift a 0%Z in let r_9 : R := Rmult r_1 r_5 in let r_10 : R := Ropp r_6 in let r_11 : R := Rmult r_1 r_8 in region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> Rle r_1 1%R -> Rle r_3 1%R -> Rle r_5 1%R -> Rle r_6 1%R -> Rle r_7 1%R -> Rle r_8 1%R -> Rle (Ropp 1%R) r_1 -> Rle (Ropp 1%R) r_3 -> Rle (Ropp 1%R) r_5 -> Rle (Ropp 1%R) r_6 -> Rle (Ropp 1%R) r_7 -> Rle (Ropp 1%R) r_8 -> linked t -> valid_rw t a 9%Z -> p_rvalid_floateulers t t_1 a_1 -> is_finite32 r -> is_finite32 r_2 -> is_finite32 r_4 -> is_float32 r -> is_float32 r_2 -> is_float32 r_4 -> is_finite32 r_1 -> is_finite32 r_3 -> is_finite32 r_5 -> is_finite32 r_6 -> is_finite32 r_7 -> is_finite32 r_8 -> is_float32 r_1 -> is_float32 r_3 -> is_float32 r_5 -> is_float32 r_6 -> is_float32 r_7 -> is_float32 r_8 -> p_rotation_matrix (l_l_rmat_of_floatrmat (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt (fun_updt t_1 (shift a_2 0%Z) (Rplus (Rmult r_8 r_7) (Ropp (Rmult r_9 r_3)))) (shift a_2 1%Z) (Rplus (Rmult r_8 r_3) (Rmult r_9 r_7))) (shift a_2 2%Z) (Rmult r_10 r_5)) (shift a_2 3%Z) (Rmult r_10 r_3)) (shift a_2 4%Z) (Rmult r_6 r_7)) (shift a_2 5%Z) r_1) (shift a_2 6%Z) (Rplus (Rmult r_5 r_7) (Rmult r_11 r_3))) (shift a_2 7%Z) (Rplus (Rmult r_5 r_3) (Ropp (Rmult r_11 r_7)))) (shift a_2 8%Z) (Rmult r_6 r_8)) a).
Admitted.
