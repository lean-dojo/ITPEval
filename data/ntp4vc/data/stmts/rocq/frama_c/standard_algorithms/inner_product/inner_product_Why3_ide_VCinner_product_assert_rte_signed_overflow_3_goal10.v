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
Require Import Why3.Cint.Cint.
Require Import inner_product.Axiomatic1.Axiomatic1.
Require Import inner_product.A_InnerProductAxiomatic.A_InnerProductAxiomatic.
Require Import inner_product.Compound.Compound.
Require Import inner_product.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal10 (t_1 : addr -> Z) (a : addr) (i_2 : Z) (a_1 : addr) (i_1 : Z) (i : Z) (t : Z -> Z) : let x : Z := t_1 (shift a i_2) in let x_1 : Z := t_1 (shift a_1 i_2) in let x_2 : Z := l_innerproduct t_1 a_1 a i_2 i_1 in i_2 ≤ i -> 0%Z ≤ i_2 -> i_2 < i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_2 -> is_sint32 i_1 -> p_productbounds t_1 a_1 a i -> is_sint32 x -> is_sint32 x_1 -> p_innerproductbounds t_1 a_1 a i i_1 -> valid_rd t (shift a 0%Z) i -> valid_rd t (shift a_1 0%Z) i -> is_sint32 x_2 -> - 2147483648%Z ≤ x_2 + to_sint32 (x * x_1).
Admitted.
