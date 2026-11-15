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
Theorem goal14 (a_1 : addr) (a_2 : addr) (a : addr) (t_3 : addr -> addr) (i : Z) (t_1 : addr -> Z) (t_2 : addr -> Z) (t : Z -> Z) : let a_3 : addr := shift a_1 0%Z in let a_4 : addr := shift a_2 0%Z in let a_5 : addr := shift a 0%Z in let a_6 : addr := t_3 a_5 in let a_7 : addr := shift a_6 0%Z in let a_8 : addr := t_3 a_3 in let a_9 : addr := shift a_8 0%Z in let a_10 : addr := shift a_8 i in let a_11 : addr := t_3 a_4 in let a_12 : addr := shift a_11 0%Z in let a_13 : addr -> Z := havoc t_1 t_2 a_12 l_size in let a_14 : addr := shift a_6 i in let a_15 : Z := a_13 a_14 in let a_16 : Z := a_13 a_10 in ¬ Mk_addr 0%Z 0%Z = a_2 -> ¬ to_uint32 i = l_size -> 0%Z ≤ i -> i ≤ l_size -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> framed t_3 -> linked t -> is_sint32 i -> valid_rd t a 1%Z -> valid_rd t a_1 1%Z -> valid_rd t a_2 1%Z -> valid_rd t a_3 1%Z -> valid_rd t a_4 1%Z -> valid_rd t a_7 l_size -> valid_rd t a_9 l_size -> valid_rd t a_10 1%Z -> valid_rw t a_12 l_size -> valid_rw t (shift a_11 i) 1%Z -> is_uint8 a_15 -> is_uint8 a_16 -> (¬ a_2 = a -> separated a_12 l_size a_7 l_size) -> (¬ a_2 = a_1 -> separated a_12 l_size a_9 l_size) -> a_16 = 0%Z ∨ a_16 = 1%Z -> a_16 = 0%Z ∨ valid_rd t a_5 1%Z ∧ valid_rd t a_14 1%Z ∧ (a_15 = 0%Z ∨ a_15 = 1%Z) -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < l_size -> separated a_12 l_size (shift (t_3 (shift (l_cpu_smt_mask i_1) 0%Z)) 0%Z) l_size) -> (∀(i_1 : Z), let a_17 : addr := shift a_11 i_1 in i ≤ i_1 -> i_1 < l_size -> (¬ a_13 a_17 = 0%Z) = (¬ t_2 a_17 = 0%Z)) -> (∀(i_1 : Z), 0%Z ≤ i_1 -> i_1 < i -> (t_2 (shift a_6 i_1) = 0%Z ∧ ¬ t_2 (shift a_8 i_1) = 0%Z) = (¬ a_13 (shift a_11 i_1) = 0%Z)) -> i ≤ 2147483646%Z.
Admitted.
