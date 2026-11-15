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
Theorem goal1 (s : s1_size_type_pair) (i_1 : Z) (i_3 : Z) (a : addr) (t_1 : addr -> Z) (i_2 : Z) (i : Z) (t : Z -> Z) : let x : Z := f1_size_type_pair_second s in let x_1 : Z := f1_size_type_pair_first s in let x_2 : Z := i_1 + i_3 in let x_4 : Z := i_1 + i_3 - x_1 in let x_5 : Z := Z.rem x_4 2%Z in let x_6 : Z := x_1 + x_5 in let x_7 : Z := x_1 + to_uint32 (Z.rem (to_uint32 x_4) 2%Z) in let x_9 : Z := x_1 + x_5 - i_1 in let a_1 : addr := shift a x_9 in let x_10 : Z := t_1 a_1 in let x_11 : Z := x_1 - i_1 in let a_2 : addr := shift a x_11 in let x_12 : Z := 1%Z + x_1 + x_5 - i_1 in let x_14 : Z := i_1 + x - 1%Z - x_1 - x_5 in let a_3 : addr := shift a x_12 in let x_15 : Z := i_1 + i_3 - 1%Z - x_1 - x_5 in 0%Z ≤ i_1 -> i_3 ≤ i_2 -> x ≤ i_3 -> 0%Z ≤ x_1 -> i_1 ≤ x_1 -> 0%Z ≤ x -> x_1 < x_2 -> region (base a) ≤ 0%Z -> 0%Z ≤ x_5 -> i_1 ≤ x_5 -> x_6 < x_2 -> x_6 < i_1 + x -> i_1 ≤ x_7 -> x_10 ≤ i -> i ≤ x_10 -> x_1 ≤ 4294967295%Z -> x ≤ 4294967295%Z -> x_2 ≤ 4294967295%Z + x_1 -> x_5 ≤ 4294967295%Z -> x_6 ≤ 4294967294%Z + i_1 -> x_2 ≤ 4294967296%Z + x_1 + x_5 -> x_7 ≤ 4294967295%Z + i_1 -> iss1_size_type_pair s -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_sint32 i -> is_uint32 x_1 -> is_uint32 x -> p_sorted_1' t_1 a 0%Z i_2 -> is_uint32 x_11 -> p_strictlowerbound_1' t_1 a i_3 i_2 i -> valid_rd t (shift a 0%Z) i_2 -> p_strictupperbound_1' t_1 a 0%Z x_11 i -> valid_rd t a_2 x_5 -> p_sorted_1' t_1 a_2 0%Z x_5 -> is_uint32 x_9 -> is_uint32 x_12 -> is_uint32 x_14 -> is_sint32 x_10 -> valid_rd t a_1 1%Z -> valid_rd t a_3 x_15 -> p_sorted_1' t_1 a_3 0%Z x_15 -> p_strictupperbound_1' t_1 a_2 0%Z i_1 x_10 -> p_strictlowerbound_1' t_1 a_3 x_14 x_15 x_10 -> p_lowerbound_1' t_1 a_2 i_1 x_5 x_10 -> p_upperbound_1' t_1 a_3 0%Z x_14 x_10 -> p_strictupperbound_1' t_1 a 0%Z x_1 x_10.
Admitted.
