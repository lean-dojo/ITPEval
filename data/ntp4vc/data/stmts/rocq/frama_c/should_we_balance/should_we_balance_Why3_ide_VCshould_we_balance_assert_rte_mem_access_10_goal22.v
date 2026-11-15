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
Require Import Why3.Cbits.Cbits.
Open Scope Z_scope.
Theorem goal22 (a_1 : addr) (t_3 : addr -> Z) (t_4 : addr -> addr) (a : addr) (i : Z) (t_1 : addr -> Z) (t_2 : addr -> Z) (i_1 : Z) (i_2 : Z) (t : Z -> Z) : let a_2 : addr := shift a_1 3%Z in let x : Z := t_3 a_2 in let a_3 : addr := shift a_1 4%Z in let a_4 : addr := t_4 a_3 in let a_5 : addr := t_4 (shift a_4 0%Z) in let a_6 : addr := shift a_1 1%Z in let x_1 : Z := t_3 a_6 in let x_2 : Z := t_3 (shift a_5 x_1) in let a_7 : addr := shift a_1 0%Z in let a_8 : addr := shift a i in let a_9 : addr := t_4 a_7 in let a_10 : addr := shift a_9 1%Z in let a_11 : addr := shift a_9 0%Z in let a_12 : addr := t_4 a_11 in let a_13 : addr := l_group_balance_mask a_12 in let a_14 : addr := shift a_5 0%Z in let a_15 : addr := shift a_8 0%Z in let a_16 : addr := t_4 a_15 in let a_17 : addr := shift a_16 0%Z in let a_18 : addr -> Z := havoc t_1 t_3 a_17 l_size in let a_19 : addr := t_4 (shift a_13 0%Z) in let a_20 : addr -> Z := havoc t_2 t_3 a_17 l_size in let a_21 : Z := a_20 (shift a_5 i_1) in let a_22 : Z := a_20 (shift a_19 i_1) in let a_23 : Z := a_20 a_10 in let a_24 : addr := shift a_19 0%Z in ¬ x = 2%Z -> ¬ x_2 = 0%Z -> 0%Z ≤ i -> i < l_size -> 0%Z ≤ i_2 -> i_2 ≤ l_size -> 0%Z ≤ x_1 -> x_1 < l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_4 -> linked t -> is_uint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> valid_rd t a_1 5%Z -> is_uint32 x -> is_sint32 x_1 -> valid_rd t a_3 1%Z -> valid_rd t a_6 1%Z -> valid_rd t a_2 1%Z -> valid_rd t a_7 1%Z -> valid_rd t a_8 1%Z -> valid_rd t a_4 1%Z -> valid_rd t (t_4 (shift a_1 2%Z)) 2%Z -> valid_rd t a_9 2%Z -> is_sint32 (t_3 a_10) -> valid_rd t a_11 1%Z -> valid_rd t a_12 1%Z -> valid_rd t a_13 1%Z -> is_uint8 x_2 -> valid_rd t a_14 l_size -> valid_rw t a_17 l_size -> is_uint8 (a_18 (shift a_5 (- 1%Z))) -> is_uint8 (a_18 (shift a_19 (- 1%Z))) -> is_uint8 a_21 -> is_uint8 a_22 -> is_sint32 (a_18 a_10) -> is_sint32 a_23 -> valid_rd t a_24 l_size -> separated a_17 l_size a_24 l_size -> (¬ land 7%Z a_23 = 0%Z -> i_1 = - 1%Z) -> (¬ i_1 = - 1%Z -> ¬ l_idle_cpu i_1 = 0%Z ∧ ¬ a_21 = 0%Z ∧ ¬ a_22 = 0%Z ∧ 0%Z ≤ i_1 ∧ i_1 < l_size) -> (i_1 = - 1%Z -> (∀(i_3 : Z), ¬ a_20 (shift a_19 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < l_size -> ¬ a_20 (shift a_16 i_3) = 0%Z)) -> (¬ i_1 = - 1%Z -> (∀(i_3 : Z), ¬ a_20 (shift a_5 i_3) = 0%Z -> ¬ a_20 (shift a_19 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < i_1 -> i_3 < l_size -> l_idle_cpu i_3 = 0%Z)) -> (i_1 = - 1%Z -> (∀(i_3 : Z), ¬ a_20 (shift a_5 i_3) = 0%Z -> ¬ a_20 (shift a_19 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < i_2 -> i_3 < l_size -> l_idle_cpu i_3 = 0%Z)) -> (¬ i_1 = - 1%Z -> (∀(i_3 : Z), ¬ a_20 (shift a_5 i_3) = 0%Z -> ¬ a_20 (shift a_19 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_1 ≤ i_3 -> i_3 < i_2 -> i_3 < l_size -> ¬ p_idle_core t_4 a_20 i_3)) -> (¬ i_1 = - 1%Z -> (∀(i_3 : Z), ¬ a_20 (shift a_19 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < l_size -> ¬ a_20 (shift a_16 i_3) = 0%Z ∨ ¬ p_idle_core t_4 a_20 i_3)) -> (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_14 l_size (shift (t_4 (shift (shift a i_3) 0%Z)) 0%Z) l_size) -> (∀(i_3 : Z), let a_25 : addr := shift a i_3 in 0%Z ≤ i_3 -> i_3 < l_size -> valid_rd t a_25 1%Z ∧ valid_rw t (shift (t_4 (shift a_25 0%Z)) 0%Z) l_size) -> (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> (¬ a_18 (shift a_19 i_3) = 0%Z) = (¬ a_18 (shift a_16 i_3) = 0%Z)) -> (∀(i_3 : Z), ¬ a_20 (shift a_16 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < l_size -> ¬ a_20 (shift a_19 i_3) = 0%Z) -> (∀(a_25 : addr), let a_26 : addr := l_sched_group_cpus a_25 in let a_27 : addr := shift (t_4 (shift a_26 0%Z)) 0%Z in valid_rd t a_26 1%Z ∧ valid_rd t a_27 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_27 l_size (shift (t_4 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(a_25 : addr), let a_26 : addr := l_sched_group_mask a_25 in let a_27 : addr := shift (t_4 (shift a_26 0%Z)) 0%Z in valid_rd t a_26 1%Z ∧ valid_rd t a_27 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_27 l_size (shift (t_4 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(a_25 : addr), let a_26 : addr := l_group_balance_mask a_25 in let a_27 : addr := shift (t_4 (shift a_26 0%Z)) 0%Z in valid_rd t a_26 1%Z ∧ valid_rd t a_27 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_27 l_size (shift (t_4 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(i_3 : Z), let a_25 : addr := l_cpu_smt_mask i_3 in let a_26 : addr := shift (t_4 (shift a_25 0%Z)) 0%Z in 0%Z ≤ i_3 -> i_3 < l_size -> valid_rd t a_25 1%Z ∧ valid_rd t a_26 l_size ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_26 l_size (shift (t_4 (shift (shift a i_4) 0%Z)) 0%Z) l_size)) -> valid_rd t a_15 1%Z.
Admitted.
