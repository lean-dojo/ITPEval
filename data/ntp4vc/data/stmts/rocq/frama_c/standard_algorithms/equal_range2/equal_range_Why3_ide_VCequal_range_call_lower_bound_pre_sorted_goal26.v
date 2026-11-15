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
Require Import equal_range2.Axiomatic.Axiomatic.
Require Import equal_range2.Compound.Compound.
Open Scope Z_scope.
Theorem goal26 (i_2 : Z) (i_3 : Z) (a : addr) (t_1 : addr -> Z) (i_1 : Z) (i : Z) (t : Z -> Z) : let x : Z := i_2 - i_3 in let x_1 : Z := Z.rem x 2%Z in let x_2 : Z := i_3 + x_1 in let a_1 : addr := shift a x_2 in let x_3 : Z := t_1 a_1 in let x_4 : Z := i_3 + to_uint32 (Z.rem (to_uint32 x) 2%Z) in i_2 ≤ i_1 -> i_3 ≤ i_2 -> 0%Z ≤ i_3 -> i_3 < i_2 -> region (base a) ≤ 0%Z -> 0%Z ≤ x_1 -> x_3 ≤ i -> 0%Z ≤ x_4 -> i ≤ x_3 -> i_2 ≤ 4294967295%Z + i_3 -> x_1 ≤ 4294967295%Z -> x_4 ≤ 4294967295%Z -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_sint32 i -> p_sorted_1' t_1 a 0%Z i_1 -> p_strictupperbound_1' t_1 a 0%Z i_3 i -> p_strictlowerbound_1' t_1 a i_2 i_1 i -> valid_rd t (shift a 0%Z) i_1 -> is_uint32 x_2 -> is_sint32 x_3 -> valid_rd t a_1 1%Z -> p_sorted_1' t_1 (shift a i_3) 0%Z x_1.
Admitted.
