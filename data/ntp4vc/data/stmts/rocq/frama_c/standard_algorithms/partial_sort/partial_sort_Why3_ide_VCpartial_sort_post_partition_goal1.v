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
Require Import partial_sort.Compound.Compound.
Require Import partial_sort.Axiomatic.Axiomatic.
Require Import partial_sort.Axiomatic1.Axiomatic1.
Require Import partial_sort.A_Count.A_Count.
Open Scope Z_scope.
Theorem goal1 (a : addr) (t_6 : addr -> Z) (t_3 : addr -> Z) (t_5 : addr -> Z) (i_2 : Z) (i_1 : Z) (i : Z) (t : Z -> Z) (p : bool) (t_1 : Z -> Z) (t_2 : addr -> Z) (t_8 : addr -> Z) (t_4 : addr -> Z) (t_7 : addr -> Z) : let a_1 : addr := shift a 0%Z in let x : Z := t_6 a_1 in let a_2 : addr -> Z := havoc t_3 t_5 a_1 i_2 in i_1 ≤ i -> 0%Z ≤ i_1 -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_sint32 (t_5 a_1) -> is_sint32 x -> valid_rw t a_1 i -> (if decide (0%Z < i_1) then p = false ∧ t_1 = t ∧ havoc t_2 t_8 a_1 i_1 = t_5 ∧ havoc t_3 t_5 a_1 i = t_6 ∧ havoc t_4 a_2 a_1 i_1 = t_7 ∧ i_2 ≤ i ∧ i ≤ i_2 ∧ i_1 ≤ i_2 ∧ p_sorted_1' t_7 a 0%Z i_1 ∧ p_isheap t_5 a i_1 ∧ p_isheap t_6 a i_1 ∧ p_multisetunchanged_1' t_5 t_8 a 0%Z i_1 ∧ p_multisetunchanged_1' t_6 t_8 a 0%Z i_2 ∧ p_unchanged_1' t_6 t_8 a i_2 i ∧ valid_rw t_1 a_1 i_1 ∧ p_upperbound_1' t_6 a 0%Z i_1 x ∧ p_lowerbound_1' t_6 a i_1 i_2 x ∧ p_multisetunchanged_1' t_7 a_2 a 0%Z i_1 else t_8 = t_7) -> p_partition t_7 a i_1 i.
Admitted.
