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
Require Import float_rmat_integrate_fi.Axiomatic15.Axiomatic15.
Require Import Why3.Cmath.Cmath.
Require Import Why3.Cfloat.Cfloat.
Require Import float_rmat_integrate_fi.Compound.Compound.
Require Import float_rmat_integrate_fi.S5_FloatRMat.S5_FloatRMat.
Open Scope Z_scope.
Theorem goal0 (a : addr) (a_1 : addr) (t : Z -> Z) (t_1 : addr -> R) (fact0 : region (base a) ≤ 0%Z) (fact1 : region (base a_1) ≤ 0%Z) (fact2 : linked t) (fact3 : valid_rw t a 9%Z) (fact4 : p_rvalid_floatrates t t_1 a_1) (fact5 : is_float32 (t_1 (shift a_1 0%Z))) (fact6 : is_float32 (t_1 (shift a_1 1%Z))) (fact7 : is_float32 (t_1 (shift a_1 2%Z))) : p_rvalid_floatrmat t t_1 a.
Admitted.
