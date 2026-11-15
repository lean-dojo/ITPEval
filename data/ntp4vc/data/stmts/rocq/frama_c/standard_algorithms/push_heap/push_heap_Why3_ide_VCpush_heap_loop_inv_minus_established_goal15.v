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
Theorem goal15 (i : Z) (a : addr) (t_1 : addr -> Z) (t : Z -> Z) : let x : Z := i - 1%Z in let x_1 : Z := l_heapparent x in let a_1 : addr := shift a x_1 in let x_2 : Z := t_1 a_1 in let a_2 : addr := shift a x in let x_3 : Z := t_1 a_2 in let a_3 : addr := shift a (to_uint32 x) in let m : addr -> Z := fun_updt t_1 a_2 x_2 in 0%Z < i -> region (base a) ≤ 0%Z -> 0%Z < x_1 -> x_2 < x_3 -> 2%Z ≤ i -> linked t -> is_uint32 i -> valid_rw t (shift a 0%Z) i -> is_uint32 x_1 -> p_isheap t_1 a x -> is_uint32 (l_heapparent x_1) -> is_sint32 x_3 -> is_sint32 x_2 -> valid_rd t a_3 1%Z -> valid_rd t a_1 1%Z -> valid_rw t a_3 1%Z -> is_sint32 (m a_1) -> p_multisetminus m t_1 a i x_3.
Admitted.
