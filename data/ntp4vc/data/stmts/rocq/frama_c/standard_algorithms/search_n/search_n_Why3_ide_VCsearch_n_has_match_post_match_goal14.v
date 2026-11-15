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
Theorem goal14 (t_1 : addr -> Z) (a : addr) (i : Z) (i_6 : Z) (i_1 : Z) (i_2 : Z) (t : Z -> Z) (i_3 : Z) (i_4 : Z) (i_5 : Z) (i_7 : Z) : let x : Z := t_1 (shift a (i - 1%Z)) in let x_1 : Z := 1%Z + i_6 in let x_2 : Z := i_1 + i_2 in let a_1 : addr := shift a i_6 in let x_3 : Z := to_uint32 x_1 in region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> is_uint32 i_6 -> is_sint32 i_7 -> p_hasconstantsubrange t_1 a i_4 i_2 i_7 -> valid_rd t (shift a 0%Z) i_4 -> is_sint32 x -> (if decide (0%Z < i_2) then if decide (i_2 ≤ i_4) then i_5 = i_3 ∧ i_5 = i_4 ∧ i ≤ x_1 ∧ p_constantrange t_1 a i i_6 i_7 ∧ ¬ p_hasconstantsubrange t_1 a i_6 i_2 i_7 ∧ (if decide (i_6 < i_5) then i_1 = i ∧ x_2 = x_1 ∧ t_1 a_1 = i_7 ∧ i_1 ≤ x_3 ∧ i_6 ≤ 4294967294%Z ∧ x_3 ≤ 4294967295%Z + i_1 ∧ valid_rd t a_1 1%Z else i_5 = i_1) ∧ (0%Z < i -> ¬ x = i_7) else i_4 = i_1 else i_1 = 0%Z) -> p_constantrange t_1 a i_1 x_2 i_7.
Admitted.
