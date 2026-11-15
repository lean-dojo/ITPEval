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
Theorem goal16 (i : Z) (a : addr) (t_2 : addr -> Z) (t_1 : addr -> Z) (i_1 : Z) (t_3 : addr -> Z) (t : Z -> Z) : let x : Z := i - 1%Z in let x_1 : Z := l_heapparent x in let a_1 : addr := shift a x_1 in let x_2 : Z := t_2 a_1 in let a_2 : addr := shift a x in let x_3 : Z := t_2 a_2 in let m : addr -> Z := fun_updt t_2 a_2 x_2 in let a_3 : addr := shift a 0%Z in let a_4 : addr -> Z := havoc t_1 m a_3 i in let a_5 : addr := shift a i_1 in let a_6 : Z := a_4 a_5 in let x_4 : Z := l_heapparent i_1 in let a_7 : addr := shift a x_4 in let a_8 : Z := a_4 a_7 in let x_5 : Z := t_3 a_7 in let a_9 : addr := shift a (to_uint32 x) in 0%Z < i -> 0%Z < i_1 -> 0%Z ≤ i_1 -> region (base a) ≤ 0%Z -> 0%Z < x_1 -> x_2 < x_3 -> a_6 < x_3 -> a_8 < x_3 -> 2%Z ≤ i -> 2%Z + i_1 ≤ i -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 x_4 -> valid_rd t a_5 1%Z -> valid_rw t a_3 i -> is_uint32 x_1 -> p_isheap t_2 a x -> is_sint32 x_5 -> valid_rd t a_7 1%Z -> is_uint32 (l_heapparent x_1) -> is_sint32 x_3 -> is_sint32 x_2 -> valid_rd t a_9 1%Z -> valid_rd t a_1 1%Z -> valid_rw t a_9 1%Z -> is_sint32 (m a_1) -> is_sint32 a_6 -> is_sint32 a_8 -> p_isheap a_4 a i -> p_multisetminus a_4 t_2 a i x_3 -> p_multisetadd a_4 t_2 a i a_6 -> p_multisetretainrest_3' a_4 t_2 a i x_3 a_6 -> (if decide (a_6 < a_8) then fun_updt a_4 a_5 a_8 = t_3 ∧ valid_rw t a_5 1%Z else a_4 = t_3) -> p_multisetretainrest_3' t_3 t_2 a i x_3 x_5.
Admitted.
