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
Require Import insertion_sort.Compound.Compound.
Require Import insertion_sort.Axiomatic1.Axiomatic1.
Require Import insertion_sort.A_Count.A_Count.
Require Import insertion_sort.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal6 (i_2 : Z) (i_1 : Z) (a : addr) (t_1 : addr -> Z) (t_3 : addr -> Z) (i : Z) (t_2 : addr -> Z) (t : Z -> Z) : let x_1 : Z := i_2 - i_1 in let x_2 : Z := 1%Z + i_2 in let a_1 : addr := shift a 0%Z in let a_2 : addr := shift a i_2 in let a_3 : addr := shift a i_1 in let x_3 : Z := 1%Z + i_2 - i_1 in let a_4 : addr -> Z := havoc t_1 t_3 a_1 i in let a_5 : Z := a_4 a_2 in let a_6 : addr -> Z := havoc t_2 a_4 a_3 x_3 in i_2 ≤ i -> 0%Z ≤ i_1 -> 0%Z ≤ i_2 -> i_2 < i -> i_1 ≤ i_2 -> region (base a) ≤ 0%Z -> i_2 ≤ 4294967294%Z -> i_2 ≤ 4294967295%Z + i_1 -> to_uint32 x_1 ≤ 4294967294%Z -> linked t -> is_uint32 i -> is_uint32 i_1 -> is_uint32 i_2 -> is_uint32 x_2 -> valid_rd t a_1 i_2 -> valid_rd t a_2 1%Z -> valid_rw t a_1 i -> valid_rw t a_3 x_3 -> is_sint32 a_5 -> p_sorted_1' a_4 a 0%Z i_2 -> p_unchanged_1' a_4 t_3 a i_2 i -> p_multisetunchanged_1' a_4 t_3 a 0%Z i_2 -> p_upperbound_1' a_4 a 0%Z i_1 a_5 -> p_strictlowerbound_1' a_4 a i_1 i_2 a_5 -> p_equalranges_4' a_6 a_4 a_3 0%Z x_1 1%Z -> p_equalranges_4' a_6 a_4 a_3 x_1 x_3 0%Z -> p_sorted_1' a_6 a 0%Z x_2.
Admitted.
