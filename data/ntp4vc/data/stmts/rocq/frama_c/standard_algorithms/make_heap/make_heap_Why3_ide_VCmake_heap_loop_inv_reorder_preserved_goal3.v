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
Theorem goal3 (i_1 : Z) (a : addr) (t_1 : addr -> Z) (t_3 : addr -> Z) (i : Z) (t_2 : addr -> Z) (t : Z -> Z) : let x : Z := 1%Z + i_1 in let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_3 a_1 i in let a_3 : addr -> Z := havoc t_2 a_2 a_1 x in 0%Z < i -> 0%Z < i_1 -> i_1 ≤ i -> i_1 < i -> region (base a) ≤ 0%Z -> i_1 ≤ 4294967294%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 x -> valid_rw t a_1 i -> valid_rw t a_1 x -> p_isheap a_2 a i_1 -> p_multisetunchanged_1' a_2 t_3 a 0%Z x -> p_unchanged_1' a_2 t_3 a x i -> p_isheap a_3 a x -> p_multisetunchanged_1' a_3 a_2 a 0%Z x -> p_multisetunchanged_1' a_3 t_3 a 0%Z (2%Z + i_1).
Admitted.
