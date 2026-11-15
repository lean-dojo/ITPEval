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
Require Import should_we_balance.A_thread_variables_properties.A_thread_variables_properties.
Require Import should_we_balance.Compound.Compound.
Require Import should_we_balance.A_schedule_cpumask.A_schedule_cpumask.
Open Scope Z_scope.
Theorem goal0 (t_3 : addr -> addr) (a : addr) (a_1 : addr) (a_2 : addr) (t_1 : addr -> Z) (t_2 : addr -> Z) (i : Z) (i_1 : Z) (t : Z -> Z) : let a_3 : addr := t_3 (shift a 0%Z) in let a_4 : addr := shift a_3 0%Z in let a_5 : addr := t_3 (shift a_1 0%Z) in let a_6 : addr := shift a_5 0%Z in let a_7 : addr := t_3 (shift a_2 0%Z) in let a_8 : addr := shift a_7 0%Z in let a_9 : addr -> Z := havoc t_1 t_2 a_8 l_size in ¬ Mk_addr 0%Z 0%Z = a_2 -> to_uint32 i = l_size -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i_1 < l_size -> i ≤ l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> framed t_3 -> linked t -> is_sint32 i -> valid_rd t a 1%Z -> valid_rd t a_1 1%Z -> valid_rd t a_2 1%Z -> valid_rd t a_4 l_size -> valid_rd t a_6 l_size -> valid_rw t a_8 l_size -> p_idle_core t_3 a_9 i_1 -> (¬ a_2 = a -> separated a_8 l_size a_4 l_size) -> (¬ a_2 = a_1 -> separated a_8 l_size a_6 l_size) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < l_size -> separated a_8 l_size (shift (t_3 (shift (l_cpu_smt_mask i_2) 0%Z)) 0%Z) l_size) -> (∀(i_2 : Z), let a_10 : addr := shift a_7 i_2 in i ≤ i_2 -> i_2 < l_size -> (¬ a_9 a_10 = 0%Z) = (¬ t_2 a_10 = 0%Z)) -> (∀(i_2 : Z), 0%Z ≤ i_2 -> i_2 < i -> (t_2 (shift a_3 i_2) = 0%Z ∧ ¬ t_2 (shift a_5 i_2) = 0%Z) = (¬ a_9 (shift a_7 i_2) = 0%Z)) -> p_idle_core t_3 t_2 i_1.
Admitted.
