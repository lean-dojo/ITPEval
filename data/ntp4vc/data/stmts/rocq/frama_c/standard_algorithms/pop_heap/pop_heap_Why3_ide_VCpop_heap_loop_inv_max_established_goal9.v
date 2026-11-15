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
Theorem goal9 (i : Z) (t_1 : addr -> Z) (a : addr) (i_1 : Z) (t : Z -> Z) : let x : Z := i - 1%Z in let x_1 : Z := t_1 (shift a x) in let a_1 : addr := shift a 0%Z in let x_2 : Z := t_1 a_1 in 0%Z < i -> 0%Z < i_1 -> region (base a) ≤ 0%Z -> x_1 < x_2 -> 2%Z ≤ i -> linked t -> is_uint32 i -> is_uint32 i_1 -> p_isheap t_1 a i -> is_sint32 x_2 -> p_heapmaximumchild t_1 a i 0%Z i_1 -> valid_rd t a_1 1%Z -> valid_rw t a_1 i -> is_sint32 (t_1 (shift a (l_heapparent 0%Z))) -> is_sint32 x_1 -> valid_rd t (shift a (to_uint32 x)) 1%Z -> (2%Z + i_1 ≤ i -> l_heapparent i_1 = 0%Z) -> p_upperbound_1' t_1 a 0%Z i x_2.
Admitted.
