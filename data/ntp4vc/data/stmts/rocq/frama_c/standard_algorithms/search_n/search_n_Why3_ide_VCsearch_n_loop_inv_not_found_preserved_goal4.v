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
Require Import search_n.Compound.Compound.
Require Import search_n.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal4 (i_4 : Z) (a : addr) (t_1 : addr -> Z) (i : Z) (i_2 : Z) (i_3 : Z) (t : Z -> Z) (i_1 : Z) (i_5 : Z) : let x : Z := 1%Z + i_4 in let a_1 : addr := shift a i_4 in let x_1 : Z := t_1 a_1 in let x_2 : Z := t_1 (shift a (i - 1%Z)) in 0%Z < i_2 -> i_2 ≤ i_3 -> i_4 < i_3 -> region (base a) ≤ 0%Z -> i_4 ≤ 4294967294%Z -> i ≤ x -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_sint32 i_5 -> is_uint32 x -> is_sint32 x_1 -> p_constantrange t_1 a i i_4 i_5 -> ¬ p_hasconstantsubrange t_1 a i_4 i_2 i_5 -> valid_rd t (shift a 0%Z) i_3 -> valid_rd t a_1 1%Z -> is_sint32 x_2 -> (0%Z < i -> ¬ x_2 = i_5) -> ¬ x_1 = i_5 ∨ i_1 = i ∧ ¬ i_1 + i_2 = x ∧ i_1 ≤ x ∧ i_4 ≤ 4294967294%Z + i_1 -> ¬ p_hasconstantsubrange t_1 a x i_2 i_5.
Admitted.
