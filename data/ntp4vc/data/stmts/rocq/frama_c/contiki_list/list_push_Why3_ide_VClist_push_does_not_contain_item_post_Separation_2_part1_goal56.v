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
Require Import contiki_list.Compound.Compound.
Require Import contiki_list.S1_list.S1_list.
Require Import contiki_list.Axiomatic.Axiomatic.
Require Import contiki_list.A_Index_of_item.A_Index_of_item.
Require Import contiki_list.Axiomatic1.Axiomatic1.
Open Scope Z_scope.
Theorem goal56 (i : Z) (i_1 : Z) (t_3 : addr -> addr) (a_3 : addr) (a_4 : addr) (a_2 : addr) (t_2 : addr -> addr) (a : addr) (a_1 : addr) (i_3 : Z) (i_2 : Z) (t : Z -> Z) (t_1 : addr -> R) : let x : Z := i - 1%Z in let x_1 : Z := i + i_1 - 1%Z in let x_2 : Z := l_index_of t_3 a_3 a_4 x x_1 in let x_3 : Z := 1%Z + x_2 in let x_4 : Z := i + i_1 in let a_5 : addr := shift a_4 0%Z in let a_6 : addr := t_3 a_2 in let a_7 : addr := shift a_4 x in let a_8 : addr -> addr := havoc t_2 (fun_updt (fun_updt t_3 a_2 a) (shift (t_3 (shift a_4 (x_2 - 1%Z))) 0%Z) a_1) (shift a_4 x_2) (i + i_1 - 1%Z - x_2) in let a_9 : addr := a_8 a_2 in let a_10 : addr -> addr := fun_updt (fun_updt a_8 (shift a_3 0%Z) a_9) a_7 a_3 in let a_11 : addr -> addr := fun_updt a_10 a_2 a_3 in ¬ i_3 = i_2 -> ¬ Mk_addr 0%Z 0%Z = a_3 -> x_3 = x_4 -> 0%Z < i -> 0%Z ≤ i_1 -> i_2 < x_4 -> i_3 < x_4 -> region (base a_2) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> x_2 < x_4 -> i_1 ≤ 2147483645%Z -> x_4 ≤ 2147483646%Z -> i ≤ 1%Z + i_2 -> i ≤ 1%Z + i_3 -> i ≤ x_3 -> framed t_3 -> linked t -> is_sint32 i -> is_sint32 i_1 -> valid_rw t a_2 1%Z -> valid_rw t a_3 4%Z -> separated a_2 1%Z a_3 4%Z -> is_sint32 x -> valid_rw t a_5 2147483646%Z -> separated a_2 1%Z a_5 2147483646%Z -> separated a_3 4%Z a_5 2147483646%Z -> separated a_6 4%Z a_5 2147483646%Z -> valid_rw t a_7 i_1 -> p_linked_n t t_3 a_6 a_4 x i_1 (Mk_addr 0%Z 0%Z) -> is_sint32 x_2 -> separated a_9 4%Z a_5 2147483646%Z -> eqs1_list (load_s1_list a_3 t_1 a_8) (load_s1_list a_3 t_1 t_3) -> p_linked_n t a_8 a_9 a_4 x i_1 (Mk_addr 0%Z 0%Z) -> p_unchanged t a_8 t_1 t t_3 t_1 a_4 x x_1 -> p_unchanged t a_11 t_1 t a_10 t_1 a_4 x x_4 -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> ¬ t_3 (shift a_4 i_4) = a_3) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> is_sint32 i_4 -> ¬ t_3 (shift a_4 i_4) = a_3) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated a_2 1%Z (t_3 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated (t_3 (shift a_4 i_4)) 4%Z a_5 2147483646%Z) -> (∀(i_4 : Z), let a_12 : addr := t_3 (shift a_4 i_4) in ¬ a_12 = a_3 -> i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated a_3 4%Z a_12 4%Z) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i ≤ 1%Z + i_4 -> i ≤ 1%Z + i_5 -> 2%Z + i_4 ≤ x_4 -> 2%Z + i_5 ≤ x_4 -> ¬ t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i ≤ 1%Z + i_4 -> i ≤ 1%Z + i_5 -> 2%Z + i_4 ≤ x_4 -> 2%Z + i_5 ≤ x_4 -> separated (t_3 (shift a_4 i_5)) 4%Z (t_3 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> ¬ a_8 (shift a_4 i_4) = a_3) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated a_2 1%Z (a_8 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated a_3 4%Z (a_8 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i ≤ 1%Z + i_4 -> 2%Z + i_4 ≤ x_4 -> separated (a_8 (shift a_4 i_4)) 4%Z a_5 2147483646%Z) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i ≤ 1%Z + i_4 -> i ≤ 1%Z + i_5 -> 2%Z + i_4 ≤ x_4 -> 2%Z + i_5 ≤ x_4 -> ¬ a_8 (shift a_4 i_5) = a_8 (shift a_4 i_4)) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i ≤ 1%Z + i_4 -> i ≤ 1%Z + i_5 -> 2%Z + i_4 ≤ x_4 -> 2%Z + i_5 ≤ x_4 -> separated (a_8 (shift a_4 i_5)) 4%Z (a_8 (shift a_4 i_4)) 4%Z) -> separated (a_11 (shift a_4 i_3)) 4%Z (a_11 (shift a_4 i_2)) 4%Z.
Admitted.
