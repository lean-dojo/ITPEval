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
Theorem goal35 (t_3 : addr -> addr) (a_3 : addr) (i_2 : Z) (i : Z) (i_1 : Z) (t_2 : addr -> addr) (a_2 : addr) (a : addr) (a_1 : addr) (t : Z -> Z) (t_1 : addr -> R) : let a_4 : addr := t_3 (shift a_3 i_2) in let x : Z := 1%Z + i + i_1 in let x_1 : Z := l_index_of t_3 a_4 a_3 i_1 x in let x_2 : Z := x_1 - 1%Z in let a_5 : addr := shift a_3 x_2 in let a_6 : addr := t_3 a_5 in let a_7 : addr -> addr := havoc t_2 (fun_updt (fun_updt t_3 a_2 a) (shift a_6 0%Z) a_1) (shift a_3 x_1) (1%Z + i + i_1 - x_1) in let a_8 : addr -> addr := fun_updt a_7 (shift a_4 0%Z) (Mk_addr 0%Z 0%Z) in let a_9 : addr := a_8 a_2 in let a_10 : addr := a_8 (shift a_3 (i + i_1 - 1%Z)) in let x_3 : Z := i + i_1 in let x_4 : Z := 1%Z + i in let a_11 : addr := shift a_3 0%Z in let a_12 : addr := t_3 a_2 in let a_13 : addr := a_7 a_2 in ¬ a_4 = Mk_addr 0%Z 0%Z -> ¬ x = x_1 -> ¬ a_9 = Mk_addr 0%Z 0%Z -> ¬ a_10 = Mk_addr 0%Z 0%Z -> 0%Z ≤ i_1 -> i_1 ≤ i_2 -> i_2 ≤ x_3 -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> i_1 ≤ x_1 -> x_1 ≤ x_3 -> - 1%Z ≤ i -> i ≤ 2147483644%Z -> i_1 ≤ 2147483645%Z -> x_3 ≤ 2147483644%Z -> x_1 ≤ x -> framed t_3 -> linked t -> is_sint32 i -> is_sint32 i_1 -> valid_rw t a_2 1%Z -> is_sint32 x_4 -> valid_rw t a_11 2147483646%Z -> valid_rw t (shift a_3 i_1) x_4 -> valid_rw t a_4 4%Z -> separated a_2 1%Z a_11 2147483646%Z -> separated a_12 4%Z a_11 2147483646%Z -> separated a_2 1%Z a_4 4%Z -> separated a_4 4%Z a_11 2147483646%Z -> p_linked_n t t_3 a_12 a_3 i_1 x_4 (Mk_addr 0%Z 0%Z) -> is_sint32 x_1 -> separated a_13 4%Z a_11 2147483646%Z -> eqs1_list (load_s1_list a_4 t_1 a_7) (load_s1_list a_4 t_1 t_3) -> p_linked_n t a_8 a_9 a_3 i_1 i (Mk_addr 0%Z 0%Z) -> p_linked_n t a_8 a_9 a_3 i_1 (i - 1%Z) a_10 -> (i_1 < x_1 -> (∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> a_7 a_5 = a_6) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> p_array_swipe_left a_7 t_3 a_3 x_1 x_3) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x_3 -> ¬ a_7 (shift a_3 i_3) = a_4)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_7 (shift a_3 i_3) = a_4)) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> p_linked_n t a_7 a_13 a_3 i_1 i (Mk_addr 0%Z 0%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> p_linked_n t a_7 a_13 a_3 i_1 x_4 (Mk_addr 0%Z 0%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> p_unchanged t a_7 t_1 t t_3 t_1 a_3 i_1 x) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> p_unchanged t a_7 t_1 t t_3 t_1 a_3 i_1 x_2) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x_3 -> separated a_2 1%Z (a_7 (shift a_3 i_3)) 4%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated a_2 1%Z (a_7 (shift a_3 i_3)) 4%Z)) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x_3 -> separated a_4 4%Z (a_7 (shift a_3 i_3)) 4%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated a_4 4%Z (a_7 (shift a_3 i_3)) 4%Z)) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x_3 -> separated (a_7 (shift a_3 i_3)) 4%Z a_11 2147483646%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated (a_7 (shift a_3 i_3)) 4%Z a_11 2147483646%Z)) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_3 : Z), i_3 < x_3 -> x_1 ≤ i_3 -> eqs1_list (load_s1_list (a_7 (shift a_3 i_3)) t_1 a_7) (load_s1_list (t_3 (shift a_3 (1%Z + i_3))) t_1 t_3))) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 < x_3 -> i_4 < x_3 -> ¬ a_7 (shift a_3 i_4) = a_7 (shift a_3 i_3))) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 ≤ x_3 -> i_4 ≤ x_3 -> ¬ a_7 (shift a_3 i_4) = a_7 (shift a_3 i_3))) -> ((∃(i_3 : Z), a_4 = t_3 (shift a_3 i_3) ∧ i_1 ≤ i_3 ∧ i_3 ≤ x_3) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 < x_3 -> i_4 < x_3 -> separated (a_7 (shift a_3 i_4)) 4%Z (a_7 (shift a_3 i_3)) 4%Z)) -> ((∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> ¬ a_4 = t_3 (shift a_3 i_3)) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 ≤ x_3 -> i_4 ≤ x_3 -> separated (a_7 (shift a_3 i_4)) 4%Z (a_7 (shift a_3 i_3)) 4%Z)) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated a_2 1%Z (t_3 (shift a_3 i_3)) 4%Z) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated (t_3 (shift a_3 i_3)) 4%Z a_11 2147483646%Z) -> (∀(i_3 : Z), let a_14 : addr := t_3 (shift a_3 i_3) in ¬ a_4 = a_14 -> i_1 ≤ i_3 -> i_3 ≤ x_3 -> separated a_4 4%Z a_14 4%Z) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 ≤ x_3 -> i_4 ≤ x_3 -> ¬ t_3 (shift a_3 i_4) = t_3 (shift a_3 i_3)) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 ≤ x_3 -> i_4 ≤ x_3 -> separated (t_3 (shift a_3 i_4)) 4%Z (t_3 (shift a_3 i_3)) 4%Z) -> valid_rw t a_10 4%Z.
Admitted.
