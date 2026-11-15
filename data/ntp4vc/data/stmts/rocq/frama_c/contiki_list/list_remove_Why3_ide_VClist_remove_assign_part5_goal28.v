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
Theorem goal28 (t_2 : addr -> addr) (a_1 : addr) (a : addr) (i : Z) (i_1 : Z) (a_2 : addr) (i_2 : Z) (t : Z -> Z) (t_1 : addr -> R) : let a_3 : addr := t_2 a_1 in let a_4 : addr := shift a 0%Z in let a_5 : addr := t_2 a_4 in let x : Z := i + i_1 in let a_6 : addr := shift a_2 0%Z in let x_1 : Z := l_index_of t_2 a_5 a_2 i_1 x in ¬ a_3 = Mk_addr 0%Z 0%Z -> ¬ a_5 = Mk_addr 0%Z 0%Z -> ¬ a_5 = a_3 -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i_1 ≤ i_2 -> i_2 ≤ x -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> region (base a_5) ≤ 0%Z -> i ≤ 2147483645%Z -> framed t_2 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> valid_rw t a_1 1%Z -> ¬ invalid t a_4 1%Z -> valid_rw t a_6 2147483646%Z -> separated a_1 1%Z a_6 2147483646%Z -> separated a_3 4%Z a_6 2147483646%Z -> p_linked_n t t_2 a_3 a_2 i_1 i (Mk_addr 0%Z 0%Z) -> p_unchanged t t_2 t_1 t t_2 t_1 a_2 i_1 i_2 -> is_sint32 x_1 -> p_linked_n t t_2 a a_2 i_2 1%Z a_5 -> p_linked_n t t_2 a_3 a_2 i_1 (i_2 - i_1) a -> p_linked_n t t_2 a_5 a_2 (1%Z + i_2) (i + i_1 - 1%Z - i_2) (Mk_addr 0%Z 0%Z) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 ≤ i_2 -> ¬ t_2 (shift a_2 i_3) = a_5) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x -> separated a_1 1%Z (t_2 (shift a_2 i_3)) 4%Z) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < i_2 -> separated a_5 4%Z (t_2 (shift a_2 i_3)) 4%Z) -> (∀(i_3 : Z), i_1 ≤ i_3 -> i_3 < x -> separated (t_2 (shift a_2 i_3)) 4%Z a_6 2147483646%Z) -> (∀(i_3 : Z), let a_7 : addr := t_2 (shift a_2 i_3) in ¬ a_7 = a_5 -> i_1 ≤ i_3 -> i_3 < x -> separated a_5 4%Z a_7 4%Z) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 < x -> i_4 < x -> ¬ t_2 (shift a_2 i_4) = t_2 (shift a_2 i_3)) -> (∀(i_4 : Z) (i_3 : Z), ¬ i_4 = i_3 -> i_1 ≤ i_3 -> i_1 ≤ i_4 -> i_3 < x -> i_4 < x -> separated (t_2 (shift a_2 i_4)) 4%Z (t_2 (shift a_2 i_3)) 4%Z) -> a_4 = a_1 ∨ shift (t_2 (shift a_2 (x_1 - 1%Z))) 0%Z = a_4 ∨ included a_4 1%Z (shift a_2 x_1) (i + i_1 - x_1).
Admitted.
