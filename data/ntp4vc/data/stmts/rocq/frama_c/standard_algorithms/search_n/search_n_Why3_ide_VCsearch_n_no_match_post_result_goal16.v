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
Theorem goal16 (t_1 : addr -> Z) (a : addr) (i : Z) (i_7 : Z) (i_3 : Z) (t : Z -> Z) (i_1 : Z) (i_2 : Z) (i_4 : Z) (i_5 : Z) (i_6 : Z) (i_8 : Z) : let x : Z := t_1 (shift a (i - 1%Z)) in let x_1 : Z := 1%Z + i_7 in let a_1 : addr := shift a i_7 in let x_2 : Z := i_3 + to_uint32 x_1 in region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> is_uint32 i_6 -> is_uint32 i_7 -> is_sint32 i_8 -> ¬ p_hasconstantsubrange t_1 a i_5 i_3 i_8 -> valid_rd t (shift a 0%Z) i_5 -> is_sint32 x -> (if decide (0%Z < i_3) then if decide (i_3 ≤ i_5) then i_5 = i_4 ∧ i_6 = i_4 ∧ i_6 = i_5 ∧ i ≤ x_1 ∧ p_constantrange t_1 a i i_7 i_8 ∧ ¬ p_hasconstantsubrange t_1 a i_7 i_3 i_8 ∧ (if decide (i_7 < i_5) then i + i_3 = x_1 ∧ i_1 + i_3 = x_1 ∧ i_2 + i_3 = x_1 ∧ t_1 a_1 = i_8 ∧ i_7 < x_2 ∧ i_7 ≤ 4294967294%Z ∧ x_2 ≤ 4294967296%Z + i_7 ∧ valid_rd t a_1 1%Z else i_5 = i_2) ∧ (0%Z < i -> ¬ x = i_8) else i_5 = i_2 else i_2 = 0%Z) -> i_5 = i_2.
Admitted.
