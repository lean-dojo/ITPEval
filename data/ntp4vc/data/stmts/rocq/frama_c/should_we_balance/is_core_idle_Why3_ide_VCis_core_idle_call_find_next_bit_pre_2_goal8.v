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
Require Import should_we_balance.A_schedule_cpumask.A_schedule_cpumask.
Require Import should_we_balance.Compound.Compound.
Require Import should_we_balance.A_thread_variables_properties.A_thread_variables_properties.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal8 (i_2 : Z) (t_2 : addr -> addr) (i : Z) (i_1 : Z) (a : addr) (t : Z -> Z) (t_1 : addr -> Z) : let a_1 : addr := shift (l_cpu_smt_mask i_2) 0%Z in let a_2 : addr := t_2 a_1 in ¬ l_idle_cpu i_2 = 0%Z -> 0%Z ≤ i -> i < l_size -> 0%Z ≤ i_1 -> 0%Z ≤ i_2 -> i_2 < l_size -> i_1 ≤ l_size -> region (base a) ≤ 0%Z -> framed t_2 -> linked t -> is_uint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> valid_rd t a_1 1%Z -> (∀(i_3 : Z), ¬ t_1 (shift a_2 i_3) = 0%Z -> 0%Z ≤ i_3 -> i_3 < i_1 -> ¬ l_idle_cpu i_3 = 0%Z) -> (∀(i_3 : Z), let a_3 : addr := shift a i_3 in 0%Z ≤ i_3 -> i_3 < l_size -> valid_rd t a_3 1%Z ∧ valid_rw t (shift (t_2 (shift a_3 0%Z)) 0%Z) l_size) -> (∀(a_3 : addr), let a_4 : addr := l_sched_group_cpus a_3 in let a_5 : addr := shift (t_2 (shift a_4 0%Z)) 0%Z in valid_rd t a_4 1%Z ∧ valid_rd t a_5 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_5 l_size (shift (t_2 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(a_3 : addr), let a_4 : addr := l_sched_group_mask a_3 in let a_5 : addr := shift (t_2 (shift a_4 0%Z)) 0%Z in valid_rd t a_4 1%Z ∧ valid_rd t a_5 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_5 l_size (shift (t_2 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(a_3 : addr), let a_4 : addr := l_group_balance_mask a_3 in let a_5 : addr := shift (t_2 (shift a_4 0%Z)) 0%Z in valid_rd t a_4 1%Z ∧ valid_rd t a_5 l_size ∧ (∀(i_3 : Z), 0%Z ≤ i_3 -> i_3 < l_size -> separated a_5 l_size (shift (t_2 (shift (shift a i_3) 0%Z)) 0%Z) l_size)) -> (∀(i_3 : Z), let a_3 : addr := l_cpu_smt_mask i_3 in let a_4 : addr := shift (t_2 (shift a_3 0%Z)) 0%Z in 0%Z ≤ i_3 -> i_3 < l_size -> valid_rd t a_3 1%Z ∧ valid_rd t a_4 l_size ∧ (∀(i_4 : Z), 0%Z ≤ i_4 -> i_4 < l_size -> separated a_4 l_size (shift (t_2 (shift (shift a i_4) 0%Z)) 0%Z) l_size)) -> valid_rd t (shift a_2 0%Z) l_size.
Admitted.
