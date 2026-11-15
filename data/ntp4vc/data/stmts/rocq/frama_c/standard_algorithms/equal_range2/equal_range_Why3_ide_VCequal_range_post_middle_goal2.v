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
Require Import equal_range2.S1_size_type_pair.S1_size_type_pair.
Require Import Why3.Cint.Cint.
Require Import equal_range2.Axiomatic.Axiomatic.
Require Import equal_range2.Compound.Compound.
Open Scope Z_scope.
Theorem goal2 (s : s1_size_type_pair) (i_8 : Z) (i_10 : Z) (a : addr) (t_1 : addr -> Z) (i_7 : Z) (i_11 : Z) (t : Z -> Z) (i_1 : Z) (i_2 : Z) (i_3 : Z) (i_4 : Z) (i_5 : Z) (i_6 : Z) (i_9 : Z) (i : Z) (p_1 : bool) (p_2 : bool) (p_3 : bool) (p : bool) : let x : Z := f1_size_type_pair_first s in let x_2 : Z := i_8 - i_10 in let x_3 : Z := Z.rem x_2 2%Z in let x_4 : Z := i_10 + x_3 in let x_5 : Z := f1_size_type_pair_second s in let a_1 : addr := shift a x_4 in let x_6 : Z := t_1 a_1 in let x_7 : Z := i_10 + to_uint32 (Z.rem (to_uint32 x_2) 2%Z) in let a_2 : addr := shift a i_10 in let a_3 : addr := shift a (1%Z + i_10 + x_3) in let x_9 : Z := i_8 - 1%Z - i_10 - x_3 in let x_10 : Z := x - i_10 in let x_11 : Z := x_5 - 1%Z - i_10 - x_3 in i_8 ≤ i_7 -> i_11 ≤ i_8 -> 0%Z ≤ i_11 -> region (base a) ≤ 0%Z -> iss1_size_type_pair s -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> is_uint32 i_6 -> is_uint32 i_7 -> is_uint32 i_8 -> is_uint32 i_9 -> is_uint32 i_10 -> is_uint32 i_11 -> is_sint32 i -> p_sorted_1' t_1 a 0%Z i_7 -> p_strictupperbound_1' t_1 a 0%Z i_11 i -> p_strictlowerbound_1' t_1 a i_8 i_7 i -> valid_rd t (shift a 0%Z) i_7 -> (if decide (i_11 < i_8) then p_1 = false ∧ p_2 = false ∧ p_3 = false ∧ i_2 = i_1 ∧ i_5 = i_4 ∧ i_10 = i_9 ∧ i_11 = i_10 ∧ x = i_3 + i_10 ∧ x = i_6 + i_10 ∧ x_4 = i_4 ∧ x_4 = i_5 ∧ x_5 = 1%Z + i_1 + i_10 + x_3 ∧ x_5 = 1%Z + i_2 + i_10 + x_3 ∧ x_5 ≤ i_8 ∧ 0%Z ≤ x ∧ i_10 ≤ x ∧ 0%Z ≤ x_5 ∧ 0%Z ≤ x_3 ∧ x_4 < i_8 ∧ x ≤ x_4 ∧ x_4 < x_5 ∧ x_6 ≤ i ∧ 0%Z ≤ x_7 ∧ i ≤ x_6 ∧ x ≤ 4294967295%Z ∧ x_5 ≤ 4294967295%Z ∧ i_8 ≤ 4294967295%Z + i_10 ∧ x_3 ≤ 4294967295%Z ∧ x_4 ≤ 4294967294%Z ∧ i_8 ≤ 4294967296%Z + i_10 + x_3 ∧ x_7 ≤ 4294967295%Z ∧ valid_rd t a_2 x_3 ∧ p_sorted_1' t_1 a_2 0%Z x_3 ∧ valid_rd t a_1 1%Z ∧ valid_rd t a_3 x_9 ∧ p_sorted_1' t_1 a_3 0%Z x_9 ∧ p_strictupperbound_1' t_1 a_2 0%Z x_10 x_6 ∧ p_strictlowerbound_1' t_1 a_3 x_11 x_9 x_6 ∧ p_lowerbound_1' t_1 a_2 x_10 x_3 x_6 ∧ p_upperbound_1' t_1 a_3 0%Z x_11 x_6 else p = false ∧ x = i_11 ∧ x_5 = x) -> p_constantrange t_1 a x x_5 i.
Admitted.
