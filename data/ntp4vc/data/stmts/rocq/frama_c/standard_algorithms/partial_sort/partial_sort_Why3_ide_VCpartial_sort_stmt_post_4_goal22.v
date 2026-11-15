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
Theorem goal22 (a : addr) (t_1 : addr -> Z) (t_4 : addr -> Z) (i_2 : Z) (t_2 : addr -> Z) (i_1 : Z) (t_3 : addr -> Z) (i_3 : Z) (i : Z) (t : Z -> Z) : let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_4 a_1 i_2 in let a_3 : addr -> Z := havoc t_2 a_2 a_1 i_1 in let a_4 : addr -> Z := havoc t_3 a_3 a_1 i_2 in let x : Z := i_2 - 1%Z in let a_5 : addr := shift a x in let a_6 : Z := a_4 a_5 in let a_7 : Z := a_3 a_1 in let a_8 : addr := shift a i_3 in let a_9 : Z := a_4 a_8 in let a_10 : addr -> Z := fun_updt (fun_updt a_4 a_8 i) a_5 a_9 in let a_11 : Z := a_10 a_8 in let a_12 : Z := a_3 a_8 in let x_1 : Z := 1%Z + i_3 in a_6 = a_7 -> a_11 = a_6 -> 0%Z < i_2 -> i_2 ≤ i_1 -> i_3 ≤ i_1 -> 0%Z ≤ i_2 -> i_3 < i_1 -> i_2 ≤ i_3 -> region (base a) ≤ 0%Z -> a_12 < a_7 -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> valid_rd t a_1 1%Z -> valid_rd t a_8 1%Z -> valid_rw t a_1 i_1 -> valid_rw t a_1 i_2 -> valid_rw t a_8 1%Z -> valid_rw t a_5 1%Z -> p_isheap a_2 a i_2 -> p_multisetunchanged_1' a_2 t_4 a 0%Z i_2 -> is_sint32 a_7 -> is_sint32 a_12 -> p_isheap a_3 a i_2 -> p_multisetunchanged_1' a_3 t_4 a 0%Z i_3 -> p_unchanged_1' a_3 t_4 a i_3 i_1 -> p_upperbound_1' a_3 a 0%Z i_2 a_7 -> p_lowerbound_1' a_3 a i_2 i_3 a_7 -> is_sint32 a_9 -> is_sint32 a_6 -> p_isheap a_4 a x -> is_sint32 a_11 -> p_multisetunchanged_1' a_4 t_4 a 0%Z x_1 -> p_multisetunchanged_1' a_4 a_3 a 0%Z i_2 -> p_maxelement a_4 a i_2 x -> p_unchanged_1' a_10 a_4 a x_1 i_1 -> p_swappedinside a_10 a_4 a x i_3 x_1 -> p_multisetunchanged_1' a_10 a_4 a 0%Z x_1.
Admitted.
