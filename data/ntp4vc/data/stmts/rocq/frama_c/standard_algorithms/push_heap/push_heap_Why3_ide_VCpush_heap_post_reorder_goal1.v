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
Require Import push_heap.Compound.Compound.
Require Import push_heap.Axiomatic.Axiomatic.
Require Import push_heap.Axiomatic1.Axiomatic1.
Require Import push_heap.A_Count.A_Count.
Open Scope Z_scope.
Theorem goal1 (a : addr) (i_1 : Z) (i_5 : Z) (t_4 : addr -> Z) (i_3 : Z) (t_2 : addr -> Z) (i : Z) (t : Z -> Z) (i_2 : Z) (i_4 : Z) (p_1 : bool) (t_3 : addr -> Z) (p : bool) (t_1 : addr -> Z) : let a_1 : addr := shift a 0%Z in let x : Z := i_1 - 1%Z in let a_2 : addr := shift a i_5 in let a_3 : addr := shift a (to_uint32 x) in let x_1 : Z := t_4 a_2 in let a_4 : addr := shift a x in let x_2 : Z := t_4 a_4 in let a_5 : addr := shift a i_3 in let m : addr -> Z := fun_updt t_4 a_4 x_1 in let x_3 : Z := t_2 a_5 in let a_6 : addr := shift a i in 0%Z < i_1 -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 i_4 -> is_uint32 i_5 -> valid_rw t a_1 i_1 -> p_isheap t_4 a x -> (if decide (2%Z ≤ i_1) then p_1 = false ∧ l_heapparent x = i_5 ∧ valid_rd t a_2 1%Z ∧ valid_rd t a_3 1%Z ∧ (if decide (x_1 < x_2) then fun_updt t_2 a_5 x_2 = t_3 ∧ valid_rw t a_5 1%Z ∧ valid_rw t a_3 1%Z ∧ (if decide (0%Z < i_5) then p = false ∧ i_3 = i_2 ∧ i_4 = i_2 ∧ i_4 = i_3 ∧ l_heapparent i_3 = i ∧ havoc t_1 m a_1 i_1 = t_2 ∧ 0%Z ≤ i_3 ∧ x_3 < x_2 ∧ 2%Z + i_3 ≤ i_1 ∧ p_isheap t_2 a i_1 ∧ p_multisetadd t_2 t_4 a i_1 x_3 ∧ p_multisetminus t_2 t_4 a i_1 x_2 ∧ p_multisetretainrest_3' t_2 t_4 a i_1 x_2 x_3 ∧ (i_3 ≤ 0%Z ∨ x_2 ≤ t_2 a_6 ∧ valid_rd t a_6 1%Z) else i_5 = i_3 ∧ m = t_2) else t_4 = t_3) else t_4 = t_3) -> p_multisetunchanged_1' t_3 t_4 a 0%Z i_1.
Admitted.
