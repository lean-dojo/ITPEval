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
Theorem goal25 (a : addr) (t_1 : addr -> Z) (t_4 : addr -> Z) (i_1 : Z) (t_2 : addr -> Z) (i : Z) (t_3 : addr -> Z) (i_2 : Z) (t : Z -> Z) : let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_4 a_1 i_1 in let a_3 : addr -> Z := havoc t_2 a_2 a_1 i in let a_4 : addr -> Z := havoc t_3 a_3 a_1 i_1 in let x : Z := i_1 - 1%Z in let a_5 : Z := a_4 (shift a x) in let a_6 : Z := a_3 a_1 in let a_7 : addr := shift a i_2 in let a_8 : Z := a_3 a_7 in a_5 = a_6 -> 0%Z < i_1 -> i_1 ≤ i -> i_2 ≤ i -> 0%Z ≤ i_1 -> i_2 < i -> i_1 ≤ i_2 -> region (base a) ≤ 0%Z -> a_8 < a_6 -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> valid_rd t a_1 1%Z -> valid_rd t a_7 1%Z -> valid_rw t a_1 i -> valid_rw t a_1 i_1 -> p_isheap a_2 a i_1 -> p_multisetunchanged_1' a_2 t_4 a 0%Z i_1 -> is_sint32 a_6 -> is_sint32 a_8 -> p_isheap a_3 a i_1 -> p_multisetunchanged_1' a_3 t_4 a 0%Z i_2 -> p_unchanged_1' a_3 t_4 a i_2 i -> p_upperbound_1' a_3 a 0%Z i_1 a_6 -> p_lowerbound_1' a_3 a i_1 i_2 a_6 -> is_sint32 a_5 -> p_isheap a_4 a x -> p_multisetunchanged_1' a_4 a_3 a 0%Z i_1 -> p_maxelement a_4 a i_1 x -> p_multisetunchanged_1' a_4 t_4 a 0%Z (1%Z + i_2).
Admitted.
