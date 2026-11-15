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
Require Import should_we_balance.A_thread_variables_properties.A_thread_variables_properties.
Require Import should_we_balance.Compound.Compound.
Require Import Why3.Cint.Cint.
Require Import should_we_balance.A_schedule_cpumask.A_schedule_cpumask.
Open Scope Z_scope.
Theorem goal16 (a_1 : addr) (t_2 : addr -> Z) (t_3 : addr -> addr) (a : addr) (i : Z) (t_1 : addr -> Z) (i_1 : Z) (t : Z -> Z) : let a_2 : addr := shift a_1 3%Z in let x : Z := t_2 a_2 in let a_3 : addr := shift a_1 4%Z in let a_4 : addr := t_3 a_3 in let a_5 : addr := t_3 (shift a_4 0%Z) in let a_6 : addr := shift a_1 1%Z in let x_1 : Z := t_2 a_6 in let x_2 : Z := t_2 (shift a_5 x_1) in let a_7 : addr := shift a i in let a_8 : addr := t_3 (shift a_7 0%Z) in let a_9 : addr := shift a_8 0%Z in let a_10 : addr -> Z := havoc t_1 t_2 a_9 l_size in let a_11 : addr := shift a_1 0%Z in let a_12 : addr := t_3 a_11 in let a_13 : addr := shift a_12 0%Z in let a_14 : addr := t_3 a_13 in let a_15 : addr := l_group_balance_mask a_14 in let a_16 : addr := t_3 (shift a_15 0%Z) in let a_17 : addr := shift a_5 0%Z in let a_18 : addr := shift a_16 0%Z in ¬ x = 2%Z -> ¬ x_2 = 0%Z -> ¬ a_10 (shift a_16 i_1) = 0%Z -> 0%Z ≤ i -> i < l_size -> 0%Z ≤ i_1 -> i_1 < l_size -> 0%Z ≤ x_1 -> x_1 < l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_3 -> linked t -> is_uint32 i -> valid_rd t a_1 5%Z -> is_uint32 x -> is_sint32 x_1 -> valid_rd t a_3 1%Z -> valid_rd t a_6 1%Z -> valid_rd t a_2 1%Z -> valid_rd t a_11 1%Z -> valid_rd t a_7 1%Z -> valid_rd t a_4 1%Z -> valid_rd t (t_3 (shift a_1 2%Z)) 2%Z -> valid_rd t a_12 2%Z -> is_sint32 (t_2 (shift a_12 1%Z)) -> valid_rd t a_13 1%Z -> valid_rd t a_14 1%Z -> valid_rd t a_15 1%Z -> is_uint8 x_2 -> valid_rd t a_17 l_size -> valid_rw t a_9 l_size -> valid_rd t a_18 l_size -> separated a_9 l_size a_18 l_size -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_17 l_size (shift (t_3 (shift (shift a i_2) 0%Z)) 0%Z) l_size) -> (∀(i_2 : Z), let a_19 : addr := shift a i_2 in 0%Z ≤ i_2 -> i_2 < l_size -> valid_rd t a_19 1%Z ∧ valid_rw t (shift (t_3 (shift a_19 0%Z)) 0%Z) l_size) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> (¬ a_10 (shift a_16 i_2) = 0%Z) = (¬ a_10 (shift a_8 i_2) = 0%Z)) -> (∀(a_19 : addr), let a_20 : addr := l_sched_group_cpus a_19 in let a_21 : addr := shift (t_3 (shift a_20 0%Z)) 0%Z in valid_rd t a_20 1%Z ∧ valid_rd t a_21 l_size ∧ (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_21 l_size (shift (t_3 (shift (shift a i_2) 0%Z)) 0%Z) l_size)) -> (∀(a_19 : addr), let a_20 : addr := l_sched_group_mask a_19 in let a_21 : addr := shift (t_3 (shift a_20 0%Z)) 0%Z in valid_rd t a_20 1%Z ∧ valid_rd t a_21 l_size ∧ (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_21 l_size (shift (t_3 (shift (shift a i_2) 0%Z)) 0%Z) l_size)) -> (∀(a_19 : addr), let a_20 : addr := l_group_balance_mask a_19 in let a_21 : addr := shift (t_3 (shift a_20 0%Z)) 0%Z in valid_rd t a_20 1%Z ∧ valid_rd t a_21 l_size ∧ (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_21 l_size (shift (t_3 (shift (shift a i_2) 0%Z)) 0%Z) l_size)) -> (∀(i_2 : Z), let a_19 : addr := l_cpu_smt_mask i_2 in let a_20 : addr := shift (t_3 (shift a_19 0%Z)) 0%Z in 0%Z ≤ i_2 -> i_2 < l_size -> valid_rd t a_19 1%Z ∧ valid_rd t a_20 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_20 l_size (shift (t_3 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> ¬ a_10 (shift a_8 i_1) = 0%Z.
Admitted.
