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
Require Import contiki_list.Compound.Compound.
Require Import contiki_list.S1_list.S1_list.
Require Import Why3.Cint.Cint.
Require Import contiki_list.Axiomatic.Axiomatic.
Require Import contiki_list.Axiomatic1.Axiomatic1.
Open Scope Z_scope.
Theorem goal3 (i_1 : Z) (i_2 : Z) (t_2 : addr -> addr) (t_3 : addr -> addr) (a_4 : addr) (a_1 : addr) (i_3 : Z) (i_5 : Z) (i_4 : Z) (i : Z) (a : addr) (a_3 : addr) (t : Z -> Z) (a_2 : addr) (t_1 : addr -> R) : let x : Z := i_1 + i_2 in let a_5 : addr -> addr := havoc t_2 t_3 (shift a_4 (1%Z + i_2)) i_1 in let a_6 : addr := t_3 a_1 in let a_7 : addr := shift a_4 0%Z in let x_1 : Z := 1%Z + i_3 in let a_8 : addr -> addr := fun_updt (havoc t_2 t_3 (shift a_4 x_1) i_1) (shift a_4 i_3) (Mk_addr 0%Z 0%Z) in ¬ i_1 = 0%Z -> ¬ i_5 = i_4 -> (x = i_3) = (i = 0%Z) -> (i_3 < x) = (i = 1%Z) -> a_5 a_1 = a_6 -> i_3 ≤ i_2 -> i_2 < i_4 -> i_2 < i_5 -> i_2 ≤ i_3 -> i_3 ≤ x -> i_4 ≤ x -> i_5 ≤ x -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> x ≤ 2147483645%Z -> framed t_3 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> is_sint32 i_3 -> valid_rw t a_1 1%Z -> is_sint32 x -> valid_rw t a_7 2147483646%Z -> separated a_1 1%Z a_7 2147483646%Z -> separated a_6 4%Z a_7 2147483646%Z -> p_linked_n t t_3 a a_4 i_2 i_1 a_3 -> p_array_swipe_right a_5 t_3 a_4 x_1 (1%Z + i_1 + i_2) -> p_linked_n t a_5 a a_4 i_2 (i_3 - i_2) a_2 -> p_linked_n t a_5 a_2 a_4 x_1 (i_1 + i_2 - i_3) a_3 -> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_2 i_3 -> (∀(i_6 : Z), i_2 ≤ i_6 -> i_6 < x -> separated a_1 1%Z (t_3 (shift a_4 i_6)) 4%Z) -> (∀(i_6 : Z), i_2 ≤ i_6 -> i_6 < x -> separated (t_3 (shift a_4 i_6)) 4%Z a_7 2147483646%Z) -> (∀(i_7 : Z) (i_6 : Z), ¬ i_7 = i_6 -> i_2 ≤ i_6 -> i_2 ≤ i_7 -> i_6 < x -> i_7 < x -> ¬ t_3 (shift a_4 i_7) = t_3 (shift a_4 i_6)) -> (∀(i_7 : Z) (i_6 : Z), ¬ i_7 = i_6 -> i_2 ≤ i_6 -> i_2 ≤ i_7 -> i_6 < x -> i_7 < x -> separated (t_3 (shift a_4 i_7)) 4%Z (t_3 (shift a_4 i_6)) 4%Z) -> (∀(i_6 : Z), i_3 < i_6 -> i_6 ≤ x -> separated a_1 1%Z (a_5 (shift a_4 i_6)) 4%Z) -> (∀(i_6 : Z), i_2 ≤ i_6 -> i_6 < i + i_1 + i_2 -> separated (a_5 (shift a_4 i_6)) 4%Z a_7 2147483646%Z) -> separated (a_8 (shift a_4 i_5)) 4%Z (a_8 (shift a_4 i_4)) 4%Z.
Admitted.
