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
Theorem goal0 (t_1 : addr -> Z) (a_1 : addr) (t_2 : addr -> addr) (i : Z) (a : addr) (t : Z -> Z) : let x : Z := t_1 (shift a_1 1%Z) in let x_1 : Z := t_1 (shift a_1 3%Z) in let a_2 : addr := t_2 (shift a_1 4%Z) in let a_3 : addr := t_2 (shift a_1 0%Z) in let x_2 : Z := t_1 (shift a_3 1%Z) in let a_4 : addr := t_2 (shift a_3 0%Z) in let a_5 : addr := t_2 (shift a_2 0%Z) in let x_3 : Z := t_1 (shift a_5 x) in let a_6 : addr := shift a_5 0%Z in let a_7 : addr := t_2 (shift (l_group_balance_mask a_4) 0%Z) in let x_4 : Z := land 7%Z x_2 in 0%Z ≤ i -> i < l_size -> 0%Z ≤ x -> x < l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_2 -> linked t -> is_uint32 i -> valid_rd t a_1 5%Z -> is_uint32 x_1 -> is_sint32 x -> valid_rd t a_2 1%Z -> valid_rd t (t_2 (shift a_1 2%Z)) 2%Z -> valid_rd t a_3 2%Z -> is_sint32 x_2 -> valid_rd t a_4 1%Z -> is_uint8 x_3 -> valid_rd t a_6 l_size -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < l_size -> separated a_6 l_size (shift (t_2 (shift (shift a i_1) 0%Z)) 0%Z) l_size) -> (∀(i_1 : Z), let a_8 : addr := shift a i_1 in 0%Z ≤ i_1 -> i_1 < l_size -> valid_rd t a_8 1%Z ∧ valid_rw t (shift (t_2 (shift a_8 0%Z)) 0%Z) l_size) -> (∀(a_8 : addr), let a_9 : addr := l_sched_group_cpus a_8 in let a_10 : addr := shift (t_2 (shift a_9 0%Z)) 0%Z in valid_rd t a_9 1%Z ∧ valid_rd t a_10 l_size ∧ (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < l_size -> separated a_10 l_size (shift (t_2 (shift (shift a i_1) 0%Z)) 0%Z) l_size)) -> (∀(a_8 : addr), let a_9 : addr := l_sched_group_mask a_8 in let a_10 : addr := shift (t_2 (shift a_9 0%Z)) 0%Z in valid_rd t a_9 1%Z ∧ valid_rd t a_10 l_size ∧ (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < l_size -> separated a_10 l_size (shift (t_2 (shift (shift a i_1) 0%Z)) 0%Z) l_size)) -> (∀(a_8 : addr), let a_9 : addr := l_group_balance_mask a_8 in let a_10 : addr := shift (t_2 (shift a_9 0%Z)) 0%Z in valid_rd t a_9 1%Z ∧ valid_rd t a_10 l_size ∧ (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < l_size -> separated a_10 l_size (shift (t_2 (shift (shift a i_1) 0%Z)) 0%Z) l_size)) -> (∀(i_1 : Z), let a_8 : addr := l_cpu_smt_mask i_1 in let a_9 : addr := shift (t_2 (shift a_8 0%Z)) 0%Z in 0%Z ≤ i_1 -> i_1 < l_size -> valid_rd t a_8 1%Z ∧ valid_rd t a_9 l_size ∧ (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_9 l_size (shift (t_2 (shift (shift a i_2) 0%Z)) 0%Z) l_size)) -> x_3 = 0%Z ∨ x_1 = 2%Z ∧ ¬ x_3 = 0%Z ∨ ¬ x_1 = 2%Z ∧ ¬ x_3 = 0%Z ∧ (∀(i_1 : Z), ¬ t_1 (shift a_5 i_1) = 0%Z -> ¬ t_1 (shift a_7 i_1) = 0%Z -> 0%Z ≤ i_1 -> i_1 < l_size -> l_idle_cpu i_1 = 0%Z) ∨ ¬ x_1 = 2%Z ∧ x_4 = 0%Z ∧ ¬ x_3 = 0%Z ∧ (∃(i_1 : Z), ¬ t_1 (shift a_5 i_1) = 0%Z ∧ ¬ t_1 (shift a_7 i_1) = 0%Z ∧ 0%Z ≤ i_1 ∧ i_1 < l_size ∧ p_idle_core t_2 t_1 i_1) ∨ ¬ x_1 = 2%Z ∧ ¬ x_4 = 0%Z ∧ ¬ x_3 = 0%Z ∧ (∃(i_1 : Z), ¬ l_idle_cpu i_1 = 0%Z ∧ ¬ t_1 (shift a_5 i_1) = 0%Z ∧ ¬ t_1 (shift a_7 i_1) = 0%Z ∧ 0%Z ≤ i_1 ∧ i_1 < l_size) ∨ ¬ x_1 = 2%Z ∧ x_4 = 0%Z ∧ ¬ x_3 = 0%Z ∧ (∀(i_1 : Z), ¬ t_1 (shift a_5 i_1) = 0%Z -> ¬ t_1 (shift a_7 i_1) = 0%Z -> 0%Z ≤ i_1 -> i_1 < l_size -> ¬ p_idle_core t_2 t_1 i_1) ∧ (∃(i_1 : Z), ¬ l_idle_cpu i_1 = 0%Z ∧ ¬ t_1 (shift a_5 i_1) = 0%Z ∧ ¬ t_1 (shift a_7 i_1) = 0%Z ∧ 0%Z ≤ i_1 ∧ i_1 < l_size).
Admitted.
