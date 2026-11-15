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
Require Import binary_search.Axiomatic.Axiomatic.
Require Import binary_search.Compound.Compound.
Open Scope Z_scope.
Theorem goal0 (a : addr) (i_2 : Z) (t_1 : addr -> Z) (i_1 : Z) (t : Z -> Z) (i : Z) (i_3 : Z) : let a_1 : addr := shift a i_2 in let x : Z := t_1 a_1 in i_2 ≤ i_1 -> 0%Z ≤ i_2 -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_sint32 i -> is_sint32 i_3 -> p_sorted_1' t_1 a 0%Z i_1 -> is_sint32 x -> p_lowerbound_1' t_1 a i_2 i_1 i -> p_strictupperbound_1' t_1 a 0%Z i_2 i -> valid_rd t (shift a 0%Z) i_1 -> (if decide (i_2 < i_1) then valid_rd t a_1 1%Z ∧ (if decide (x ≤ i) then i_3 = 1%Z else i_3 = 0%Z) else i_3 = 0%Z) -> (∃(i_4 : Z), t_1 (shift a i_4) = i ∧ 0%Z ≤ i_4 ∧ i_4 < i_1) = (¬ i_3 = 0%Z).
Admitted.
