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
Require Import contiki_list.A_Index_of_item.A_Index_of_item.
Require Import contiki_list.Compound.Compound.
Require Import contiki_list.S1_list.S1_list.
Require Import Why3.Cint.Cint.
Require Import contiki_list.Axiomatic.Axiomatic.
Require Import contiki_list.Axiomatic1.Axiomatic1.
Open Scope Z_scope.
Theorem goal43 (i : Z) (i_1 : Z) (a_4 : addr) (t_3 : addr -> addr) (a_2 : addr) (a : addr) (a_1 : addr) (t_2 : addr -> addr) (a_3 : addr) (t : Z -> Z) (t_1 : addr -> R) : let x : Z := i + i_1 in let x_1 : Z := i + i_1 - 1%Z in let a_5 : addr := shift a_4 x_1 in let m : addr -> addr := fun_updt (fun_updt t_3 a_2 a) (shift (t_3 a_5) 0%Z) a_1 in let a_6 : addr -> addr := havoc t_2 m (shift a_4 x) 0%Z in let a_7 : addr -> addr := fun_updt a_6 (shift a_3 0%Z) (Mk_addr 0%Z 0%Z) in let a_8 : addr := a_7 a_2 in let a_9 : addr := a_7 a_5 in let a_10 : addr := shift a_4 0%Z in let a_11 : addr := t_3 a_2 in let a_12 : addr := m a_2 in ¬ Mk_addr 0%Z 0%Z = a_3 -> x = l_index_of t_3 a_3 a_4 i_1 x -> ¬ a_8 = Mk_addr 0%Z 0%Z -> ¬ a_9 = Mk_addr 0%Z 0%Z -> 0%Z ≤ i -> 0%Z ≤ i_1 -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> i ≤ 2147483645%Z -> i_1 ≤ 2147483645%Z -> x ≤ 2147483645%Z -> framed t_3 -> linked t -> is_sint32 i -> is_sint32 i_1 -> valid_rw t a_2 1%Z -> valid_rw t a_3 4%Z -> separated a_2 1%Z a_3 4%Z -> is_sint32 x -> valid_rw t a_10 2147483646%Z -> valid_rw t (shift a_4 i_1) i -> separated a_2 1%Z a_10 2147483646%Z -> separated a_3 4%Z a_10 2147483646%Z -> separated a_11 4%Z a_10 2147483646%Z -> p_linked_n t t_3 a_11 a_4 i_1 i (Mk_addr 0%Z 0%Z) -> separated a_12 4%Z a_10 2147483646%Z -> eqs1_list (load_s1_list a_3 t_1 a_6) (load_s1_list a_3 t_1 t_3) -> p_linked_n t a_6 a_12 a_4 i_1 i (Mk_addr 0%Z 0%Z) -> p_linked_n t a_7 a_8 a_4 i_1 i (Mk_addr 0%Z 0%Z) -> p_linked_n t a_7 a_8 a_4 i_1 (i - 1%Z) a_9 -> p_unchanged t a_6 t_1 t t_3 t_1 a_4 i_1 x -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> ¬ t_3 (shift a_4 i_2) = a_3) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> separated a_2 1%Z (t_3 (shift a_4 i_2)) 4%Z) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> separated (t_3 (shift a_4 i_2)) 4%Z a_10 2147483646%Z) -> (∀(i_2 : Z), let a_13 : addr := t_3 (shift a_4 i_2) in ¬ a_13 = a_3 -> i_1 ≤ i_2 -> i_2 < x -> separated a_3 4%Z a_13 4%Z) -> (∀(i_3 : Z) (i_2 : Z), ¬ i_3 = i_2 -> i_1 ≤ i_2 -> i_1 ≤ i_3 -> i_2 < x -> i_3 < x -> ¬ t_3 (shift a_4 i_3) = t_3 (shift a_4 i_2)) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> ¬ m (shift a_4 i_2) = a_3) -> (∀(i_3 : Z) (i_2 : Z), ¬ i_3 = i_2 -> i_1 ≤ i_2 -> i_1 ≤ i_3 -> i_2 < x -> i_3 < x -> separated (t_3 (shift a_4 i_3)) 4%Z (t_3 (shift a_4 i_2)) 4%Z) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> separated a_2 1%Z (m (shift a_4 i_2)) 4%Z) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> separated a_3 4%Z (m (shift a_4 i_2)) 4%Z) -> (∀(i_2 : Z), i_1 ≤ i_2 -> i_2 < x -> separated (m (shift a_4 i_2)) 4%Z a_10 2147483646%Z) -> (∀(i_3 : Z) (i_2 : Z), ¬ i_3 = i_2 -> i_1 ≤ i_2 -> i_1 ≤ i_3 -> i_2 < x -> i_3 < x -> ¬ m (shift a_4 i_3) = m (shift a_4 i_2)) -> (∀(i_3 : Z) (i_2 : Z), ¬ i_3 = i_2 -> i_1 ≤ i_2 -> i_1 ≤ i_3 -> i_2 < x -> i_3 < x -> separated (m (shift a_4 i_3)) 4%Z (m (shift a_4 i_2)) 4%Z) -> p_linked_n t a_7 a_9 a_4 x_1 1%Z (a_7 (shift a_9 0%Z)).
Admitted.
