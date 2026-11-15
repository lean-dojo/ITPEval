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
Theorem goal10 (a : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (i_1 : Z) (i : Z) (t : Z -> Z) : let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_2 a_1 i_1 in let a_3 : Z := a_2 a_1 in 0%Z < i_1 -> i_1 ≤ i -> 0%Z ≤ i_1 -> region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> valid_rw t a_1 i -> valid_rw t a_1 i_1 -> is_sint32 a_3 -> p_isheap a_2 a i_1 -> p_multisetunchanged_1' a_2 t_2 a 0%Z i_1 -> p_upperbound_1' a_2 a 0%Z i_1 a_3.
Admitted.
