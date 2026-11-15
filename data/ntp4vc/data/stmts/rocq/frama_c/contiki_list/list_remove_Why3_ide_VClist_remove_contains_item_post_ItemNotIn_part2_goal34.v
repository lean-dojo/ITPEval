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
Open Scope Z_scope.
Theorem goal34 (t_1 : addr -> addr) (a : addr) (a_1 : addr) (i_2 : Z) (i : Z) (i_1 : Z) (i_3 : Z) (t : Z -> Z) : let a_2 : addr := t_1 a in let a_3 : addr := t_1 (shift a_1 i_2) in let x : Z := i + i_1 in let a_4 : addr := shift a_1 0%Z in ¬ a_2 = Mk_addr 0%Z 0%Z -> ¬ a_3 = Mk_addr 0%Z 0%Z -> a_3 = a_2 -> 0%Z ≤ i -> 0%Z ≤ i_1 -> i_1 ≤ i_2 -> i_1 ≤ i_3 -> i_2 < x -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_2) ≤ 0%Z -> i ≤ 2147483645%Z -> 2%Z + i_3 ≤ x -> framed t_1 -> linked t -> is_sint32 i -> is_sint32 i_1 -> valid_rw t a 1%Z -> valid_rw t a_4 2147483646%Z -> separated a 1%Z a_4 2147483646%Z -> separated a_2 4%Z a_4 2147483646%Z -> p_linked_n t t_1 a_2 a_1 i_1 i (Mk_addr 0%Z 0%Z) -> is_sint32 (l_index_of t_1 a_3 a_1 i_1 x) -> (∀(i_4 : Z), i_1 ≤ i_4 -> i_4 < x -> separated a 1%Z (t_1 (shift a_1 i_4)) 4%Z) -> (∀(i_4 : Z), i_1 ≤ i_4 -> i_4 < x -> separated (t_1 (shift a_1 i_4)) 4%Z a_4 2147483646%Z) -> (∀(i_4 : Z), let a_5 : addr := t_1 (shift a_1 i_4) in ¬ a_3 = a_5 -> i_1 ≤ i_4 -> i_4 < x -> separated a_3 4%Z a_5 4%Z) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i_1 ≤ i_4 -> i_1 ≤ i_5 -> i_4 < x -> i_5 < x -> ¬ t_1 (shift a_1 i_5) = t_1 (shift a_1 i_4)) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i_1 ≤ i_4 -> i_1 ≤ i_5 -> i_4 < x -> i_5 < x -> separated (t_1 (shift a_1 i_5)) 4%Z (t_1 (shift a_1 i_4)) 4%Z) -> ¬ fun_updt t_1 a (t_1 (shift a_2 0%Z)) (shift a_1 i_3) = a_3.
Admitted.
