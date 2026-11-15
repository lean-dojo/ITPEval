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
Require Import pop_heap.Axiomatic.Axiomatic.
Require Import pop_heap.Compound.Compound.
Require Import pop_heap.Axiomatic1.Axiomatic1.
Require Import pop_heap.A_Count.A_Count.
Open Scope Z_scope.
Theorem goal1 (a : addr) (t_5 : addr -> Z) (i : Z) (t_4 : addr -> Z) (i_1 : Z) (t_3 : addr -> Z) (i_3 : Z) (t : Z -> Z) (i_2 : Z) (p : bool) (p_1 : bool) (t_1 : Z -> Z) (t_2 : addr -> Z) : let a_1 : addr := shift a 0%Z in let x : Z := t_5 a_1 in let x_1 : Z := i - 1%Z in let a_2 : addr := shift a x_1 in let x_2 : Z := t_4 a_2 in let a_3 : addr := shift a (to_uint32 x_1) in let a_4 : addr := shift a i_1 in let x_3 : Z := t_3 a_2 in let a_5 : addr := shift a i_3 in 0%Z < i -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> p_isheap t_5 a i -> is_sint32 x -> valid_rw t a_1 i -> is_sint32 x_2 -> (if decide (2%Z ≤ i) then valid_rd t a_1 1%Z ∧ valid_rd t a_3 1%Z ∧ (if decide (t_5 a_2 < x) then p = false ∧ p_1 = false ∧ t_1 = t ∧ havoc t_2 t_5 a_1 x_1 = t_3 ∧ fun_updt (fun_updt t_3 a_4 x_3) a_2 x = t_4 ∧ 0%Z < i_2 ∧ 0%Z ≤ i_1 ∧ i_1 < i_3 ∧ x_3 < t_3 (shift a (l_heapparent i_1)) ∧ 2%Z + i_1 ≤ i ∧ p_isheap t_3 a i ∧ p_heapmaximumchild t_3 a i i_1 i_3 ∧ p_heapmaximumchild t_5 a i 0%Z i_2 ∧ valid_rw t_1 a_1 i ∧ valid_rw t_1 a_4 1%Z ∧ p_upperbound_1' t_3 a 0%Z i x ∧ valid_rd t_1 a_3 1%Z ∧ valid_rw t_1 a_3 1%Z ∧ (2%Z + i_2 ≤ i -> l_heapparent i_2 = 0%Z) ∧ (2%Z + i_3 ≤ i -> l_heapparent i_3 = i_1) ∧ (i ≤ 1%Z + i_3 ∨ t_3 a_5 ≤ x_3 ∧ valid_rd t_1 a_5 1%Z) else t_5 = t_4) else t_5 = t_4) -> x_2 = x.
Admitted.
