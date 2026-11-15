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
Require Import remove_copy.Axiomatic1.Axiomatic1.
Require Import remove_copy.A_Count.A_Count.
Require Import Why3.Cint.Cint.
Require Import remove_copy.Compound.Compound.
Require Import remove_copy.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal5 (t_3 : addr -> Z) (a_1 : addr) (i_5 : Z) (i : Z) (a : addr) (t_1 : addr -> Z) (i_2 : Z) (t : Z -> Z) (i_1 : Z) (i_3 : Z) (i_4 : Z) (t_2 : addr -> Z) (p : bool) : let x : Z := l_count_1' t_3 a_1 0%Z i_5 i in let x_1 : Z := 1%Z + i_5 in let a_2 : addr := shift a_1 0%Z in let a_3 : addr := shift a_1 i_5 in let a_4 : addr := shift a 0%Z in let x_2 : Z := i_5 - x in let a_5 : addr -> Z := havoc t_1 t_3 a_4 i_2 in let a_6 : Z := a_5 a_3 in let a_7 : addr := shift a x_2 in i_5 ≤ i_2 -> i_5 < i_2 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> x ≤ i_5 -> 0%Z ≤ x -> i_5 ≤ 4294967294%Z -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> is_sint32 i -> is_uint32 x_1 -> valid_rd t a_2 i_2 -> valid_rd t a_3 1%Z -> valid_rw t a_4 i_2 -> separated a_2 i_2 a 1%Z -> is_uint32 x_2 -> is_sint32 a_6 -> ¬ p_hasvalue_1' a_5 a 0%Z x_2 i -> p_unchanged_1' a_5 t_3 a_1 i_5 i_2 -> p_unchanged_1' a_5 t_3 a x_2 i_2 -> p_multisetretainrest_1' a_5 t_3 a_1 0%Z i_5 a 0%Z x_2 i -> (if decide (a_6 = i) then a_5 = t_2 ∧ i_4 + l_count_1' t_3 a_1 0%Z i_5 (t_2 a_3) = i_5 else p = false ∧ i_3 = i_1 ∧ i_1 + x = i_5 ∧ i_3 + x = i_5 ∧ i_4 + x = x_1 ∧ fun_updt a_5 a_7 a_6 = t_2 ∧ i_5 ≤ 4294967294%Z + x ∧ valid_rw t a_7 1%Z) -> p_multisetretainrest_1' t_2 t_3 a_1 0%Z x_1 a 0%Z i_4 i.
Admitted.
