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
Require Import make_heap.Compound.Compound.
Require Import make_heap.Axiomatic.Axiomatic.
Require Import make_heap.Axiomatic1.Axiomatic1.
Require Import make_heap.A_Count.A_Count.
Open Scope Z_scope.
Theorem goal1 (a : addr) (i_1 : Z) (t : Z -> Z) (i : Z) (p : bool) (t_1 : addr -> Z) (t_3 : addr -> Z) (t_2 : addr -> Z) : let a_1 : addr := shift a 0%Z in let x : Z := 1%Z + i_1 in region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> valid_rw t a_1 i -> (if decide (0%Z < i) then p = false ∧ havoc t_1 t_3 a_1 i = t_2 ∧ 0%Z < i_1 ∧ i_1 ≤ i ∧ i ≤ i_1 ∧ p_isheap t_2 a i_1 ∧ p_multisetunchanged_1' t_2 t_3 a 0%Z x ∧ p_unchanged_1' t_2 t_3 a x i else t_3 = t_2) -> p_multisetunchanged_1' t_2 t_3 a 0%Z i.
Admitted.
