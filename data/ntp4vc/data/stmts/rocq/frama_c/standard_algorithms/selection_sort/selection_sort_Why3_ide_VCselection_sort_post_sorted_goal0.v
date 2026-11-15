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
Require Import selection_sort.Compound.Compound.
Require Import selection_sort.Axiomatic1.Axiomatic1.
Require Import selection_sort.A_Count.A_Count.
Require Import selection_sort.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal0 (a : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) : let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_2 a_1 i in let a_3 : Z := a_2 (shift a (i_1 - 1%Z)) in i_1 ≤ i -> 0%Z ≤ i_1 -> i ≤ i_1 -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_sint32 (t_2 (shift a (- 1%Z))) -> valid_rw t a_1 i -> is_sint32 a_3 -> p_sorted_1' a_2 a 0%Z i_1 -> p_multisetunchanged_1' a_2 t_2 a 0%Z i -> (0%Z < i_1 -> p_lowerbound_1' a_2 a i_1 i a_3) -> p_sorted_1' (havoc t_1 t_2 a_1 i_1) a 0%Z i_1.
Admitted.
