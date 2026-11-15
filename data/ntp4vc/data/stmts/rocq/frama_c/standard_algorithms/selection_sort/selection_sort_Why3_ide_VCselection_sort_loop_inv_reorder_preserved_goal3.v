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
Theorem goal3 (a : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (i_2 : Z) (i_3 : Z) (i_1 : Z) (i : Z) (t : Z -> Z) : let a_1 : addr := shift a 0%Z in let a_2 : addr -> Z := havoc t_1 t_2 a_1 i_2 in let a_3 : addr := shift a i_3 in let a_4 : addr := shift a i_1 in let a_5 : Z := a_2 a_3 in let a_6 : addr -> Z := fun_updt (fun_updt a_2 a_3 i) a_4 a_5 in let a_7 : Z := a_6 a_3 in let a_8 : Z := a_2 a_4 in let x_1 : Z := i_1 - i_3 in let x_2 : Z := i_2 - i_3 in let a_9 : Z := a_2 (shift a (i_3 - 1%Z)) in a_7 = a_8 -> 0%Z ≤ i_1 -> i_1 < i_2 -> i_3 ≤ i_1 -> i_1 ≤ i_2 -> i_3 ≤ i_2 -> 0%Z ≤ i_3 -> i_3 < i_2 -> region (base a) ≤ 0%Z -> i_3 ≤ 4294967294%Z -> i_1 ≤ 4294967295%Z -> i_2 ≤ 4294967295%Z + i_3 -> linked t -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 i_3 -> is_uint32 x_1 -> is_sint32 (t_2 (shift a (- 1%Z))) -> valid_rw t a_1 i_2 -> valid_rd t a_3 x_2 -> is_sint32 a_8 -> is_sint32 a_5 -> is_sint32 a_9 -> p_sorted_1' a_2 a 0%Z i_3 -> is_sint32 a_7 -> p_multisetunchanged_1' a_2 t_2 a 0%Z i_2 -> p_minelement a_2 a_3 x_2 x_1 -> p_strictlowerbound_1' a_2 a_3 0%Z x_1 a_8 -> p_unchanged_1' a_6 a_2 a 0%Z i_3 -> p_unchanged_1' a_6 a_2 a (1%Z + i_1) i_2 -> p_unchanged_1' a_6 a_2 a (1%Z + i_3) i_1 -> (0%Z < i_3 -> p_lowerbound_1' a_2 a i_3 i_2 a_9) -> p_multisetunchanged_1' a_6 t_2 a 0%Z i_2.
Admitted.
