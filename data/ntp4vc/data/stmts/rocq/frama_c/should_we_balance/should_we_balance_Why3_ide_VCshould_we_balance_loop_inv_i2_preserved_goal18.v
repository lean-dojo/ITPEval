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
Theorem goal18 (a_1 : addr) (t_3 : addr -> Z) (t_4 : addr -> addr) (a : addr) (i : Z) (t_2 : addr -> Z) (t_1 : addr -> Z) (i_2 : Z) (i_3 : Z) (i_1 : Z) (t : Z -> Z) : let a_2 : addr := shift a_1 3%Z in let x : Z := t_3 a_2 in let a_3 : addr := shift a_1 4%Z in let a_4 : addr := t_4 a_3 in let a_5 : addr := shift a_4 0%Z in let a_6 : addr := t_4 a_5 in let a_7 : addr := shift a_1 1%Z in let x_1 : Z := t_3 a_7 in let x_2 : Z := t_3 (shift a_6 x_1) in let a_8 : addr := shift a i in let a_9 : addr := shift a_8 0%Z in let a_10 : addr := t_4 a_9 in let a_11 : addr := shift a_10 0%Z in let a_12 : addr -> Z := havoc t_2 t_3 a_11 l_size in let a_13 : addr := shift a_1 0%Z in let a_14 : addr := t_4 a_13 in let a_15 : addr := shift a_14 0%Z in let a_16 : addr := t_4 a_15 in let a_17 : addr := l_group_balance_mask a_16 in let a_18 : addr := t_4 (shift a_17 0%Z) in let a_19 : addr := shift a_14 1%Z in let a_20 : addr := shift a_6 0%Z in let a_21 : addr -> Z := havoc t_1 t_3 a_11 l_size in let a_22 : addr := shift a_6 (- 1%Z) in let a_23 : addr := shift a_18 (- 1%Z) in let a_24 : Z := a_12 (shift a_10 i_2) in let a_25 : Z := a_12 (shift a_6 i_2) in let a_26 : addr := shift a_18 0%Z in let x_3 : Z := to_uint32 i_3 in l_idle_cpu i_2 = 0%Z -> ¬ x = 2%Z -> ¬ x_2 = 0%Z -> ¬ a_12 (shift a_6 i_1) = 0%Z -> ¬ a_12 (shift a_18 i_1) = 0%Z -> 0%Z ≤ i -> i < l_size -> 0%Z ≤ i_1 -> i_1 < l_size -> 0%Z ≤ i_2 -> i_1 ≤ i_2 -> i_2 < l_size -> 0%Z ≤ i_3 -> i_3 ≤ l_size -> to_uint32 i_2 < l_size -> 0%Z ≤ x_1 -> x_1 < l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> i_2 ≤ 2147483646%Z -> framed t_4 -> linked t -> is_uint32 i -> is_sint32 i_2 -> is_sint32 i_3 -> valid_rd t a_1 5%Z -> is_uint32 x -> is_sint32 (1%Z + i_2) -> is_sint32 x_1 -> valid_rd t a_3 1%Z -> valid_rd t a_7 1%Z -> valid_rd t a_2 1%Z -> valid_rd t a_13 1%Z -> valid_rd t a_8 1%Z -> valid_rd t a_4 1%Z -> valid_rd t (t_4 (shift a_1 2%Z)) 2%Z -> valid_rd t a_14 2%Z -> is_sint32 (t_3 a_19) -> valid_rd t a_9 1%Z -> valid_rd t a_5 1%Z -> valid_rd t a_15 1%Z -> valid_rd t a_16 1%Z -> valid_rd t a_17 1%Z -> is_uint8 x_2 -> valid_rd t a_11 l_size -> valid_rd t a_20 l_size -> valid_rw t a_11 l_size -> is_uint8 (a_21 a_22) -> is_uint8 (a_21 a_23) -> is_uint8 a_24 -> is_uint8 (a_12 a_22) -> is_uint8 a_25 -> is_uint8 (a_12 a_23) -> is_sint32 (a_21 a_19) -> is_sint32 (a_12 a_19) -> valid_rd t a_26 l_size -> separated a_11 l_size a_26 l_size -> ((∃(i_4 : Z), ¬ a_12 (shift a_10 i_4) = 0%Z ∧ ¬ a_12 (shift a_6 i_4) = 0%Z ∧ i_4 < l_size ∧ x_3 ≤ i_4) -> x_3 ≤ i_2) -> ((∃(i_4 : Z), ¬ a_12 (shift a_10 i_4) = 0%Z ∧ ¬ a_12 (shift a_6 i_4) = 0%Z ∧ i_4 < l_size ∧ x_3 ≤ i_4) -> ¬ a_24 = 0%Z ∧ ¬ a_25 = 0%Z) -> ((∀(i_4 : Z), i_4 < l_size -> x_3 ≤ i_4 -> a_12 (shift a_10 i_4) = 0%Z ∨ a_12 (shift a_6 i_4) = 0%Z) -> l_size = i_2) -> ((∃(i_4 : Z), ¬ a_12 (shift a_10 i_4) = 0%Z ∧ ¬ a_12 (shift a_6 i_4) = 0%Z ∧ i_4 < l_size ∧ x_3 ≤ i_4) -> (∀(i_4 : Z), i_4 < i_2 -> x_3 ≤ i_4 -> a_12 (shift a_10 i_4) = 0%Z ∨ a_12 (shift a_6 i_4) = 0%Z)) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_20 l_size (shift (t_4 (shift (shift a i_4) 0%Z)) 0%Z) l_size) -> (∀(i_4 : Z), let a_27 : addr := shift a i_4 in 0%Z ≤ i_4 -> i_4 < l_size -> valid_rd t a_27 1%Z ∧ valid_rw t (shift (t_4 (shift a_27 0%Z)) 0%Z) l_size) -> (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> (¬ a_21 (shift a_18 i_4) = 0%Z) = (¬ a_21 (shift a_10 i_4) = 0%Z)) -> (∀(i_4 : Z), ¬ a_12 (shift a_18 i_4) = 0%Z -> 0%Z ≤ i_4 -> i_4 < l_size -> ¬ a_12 (shift a_10 i_4) = 0%Z) -> (∀(i_4 : Z), ¬ a_12 (shift a_10 i_4) = 0%Z -> 0%Z ≤ i_4 -> i_4 < l_size -> ¬ a_12 (shift a_18 i_4) = 0%Z) -> (∀(i_4 : Z), ¬ a_12 (shift a_6 i_4) = 0%Z -> ¬ a_12 (shift a_18 i_4) = 0%Z -> 0%Z ≤ i_4 -> i_4 < i_3 -> i_4 < l_size -> l_idle_cpu i_4 = 0%Z) -> (∀(a_27 : addr), let a_28 : addr := l_sched_group_cpus a_27 in let a_29 : addr := shift (t_4 (shift a_28 0%Z)) 0%Z in valid_rd t a_28 1%Z ∧ valid_rd t a_29 l_size ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_29 l_size (shift (t_4 (shift (shift a i_4) 0%Z)) 0%Z) l_size)) -> (∀(a_27 : addr), let a_28 : addr := l_sched_group_mask a_27 in let a_29 : addr := shift (t_4 (shift a_28 0%Z)) 0%Z in valid_rd t a_28 1%Z ∧ valid_rd t a_29 l_size ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_29 l_size (shift (t_4 (shift (shift a i_4) 0%Z)) 0%Z) l_size)) -> (∀(a_27 : addr), let a_28 : addr := l_group_balance_mask a_27 in let a_29 : addr := shift (t_4 (shift a_28 0%Z)) 0%Z in valid_rd t a_28 1%Z ∧ valid_rd t a_29 l_size ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_29 l_size (shift (t_4 (shift (shift a i_4) 0%Z)) 0%Z) l_size)) -> (∀(i_4 : Z), let a_27 : addr := l_cpu_smt_mask i_4 in let a_28 : addr := shift (t_4 (shift a_27 0%Z)) 0%Z in 0%Z ≤ i_4 -> i_4 < l_size -> valid_rd t a_27 1%Z ∧ valid_rd t a_28 l_size ∧ (∀(i_5 : Z), 0%Z ≤ i_5 -> i_5 < l_size -> separated a_28 l_size (shift (t_4 (shift (shift a i_5) 0%Z)) 0%Z) l_size)) -> l_idle_cpu i_1 = 0%Z.
Admitted.
