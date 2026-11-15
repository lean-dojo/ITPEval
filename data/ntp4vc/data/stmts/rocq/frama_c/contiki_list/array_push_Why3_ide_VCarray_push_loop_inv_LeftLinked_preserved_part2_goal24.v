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
Theorem goal24 (i_3 : Z) (t_2 : addr -> addr) (t_3 : addr -> addr) (a_4 : addr) (i_2 : Z) (i_1 : Z) (a_1 : addr) (i : Z) (a : addr) (a_3 : addr) (t : Z -> Z) (a_2 : addr) (t_1 : addr -> R) : let x : Z := 1%Z + i_3 in let a_5 : addr -> addr := havoc t_2 t_3 (shift a_4 (1%Z + i_2)) i_1 in let a_6 : addr := t_3 a_1 in let x_1 : Z := i_1 + i_2 in let x_2 : Z := i_2 + i_3 in let x_3 : Z := 1%Z + i_2 + i_3 in let a_7 : addr := shift a_4 0%Z in let x_4 : Z := 2%Z + i_2 + i_3 in let a_8 : addr := a_5 (shift a_4 x_2) in ¬ i_1 = 0%Z -> ¬ i_3 = 0%Z -> (x = i_1) = (i = 0%Z) -> (2%Z + i_3 ≤ i_1) = (i = 1%Z) -> a_5 a_1 = a_6 -> 0%Z ≤ i_3 -> i_3 < i_1 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> region (base a_3) ≤ 0%Z -> region (base a_4) ≤ 0%Z -> - 1%Z ≤ i_3 -> x_1 ≤ 2147483645%Z -> framed t_3 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> valid_rw t a_1 1%Z -> is_sint32 x_1 -> is_sint32 x_2 -> is_sint32 x_3 -> valid_rw t a_7 2147483646%Z -> separated a_1 1%Z a_7 2147483646%Z -> separated a_6 4%Z a_7 2147483646%Z -> p_linked_n t t_3 a a_4 i_2 i_1 a_3 -> p_array_swipe_right a_5 t_3 a_4 x_4 (1%Z + i_1 + i_2) -> p_linked_n t a_5 a a_4 i_2 x a_2 -> p_linked_n t a_5 a_2 a_4 x_4 (i_1 - 1%Z - i_3) a_3 -> p_unchanged t a_5 t_1 t t_3 t_1 a_4 i_2 x_3 -> (∀(i_4 : Z), i_2 ≤ i_4 -> i_4 < x_1 -> separated a_1 1%Z (t_3 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i_2 ≤ i_4 -> i_4 < x_1 -> separated (t_3 (shift a_4 i_4)) 4%Z a_7 2147483646%Z) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i_2 ≤ i_4 -> i_2 ≤ i_5 -> i_4 < x_1 -> i_5 < x_1 -> ¬ t_3 (shift a_4 i_5) = t_3 (shift a_4 i_4)) -> (∀(i_5 : Z) (i_4 : Z), ¬ i_5 = i_4 -> i_2 ≤ i_4 -> i_2 ≤ i_5 -> i_4 < x_1 -> i_5 < x_1 -> separated (t_3 (shift a_4 i_5)) 4%Z (t_3 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i_4 ≤ x_1 -> x_4 ≤ i_4 -> separated a_1 1%Z (a_5 (shift a_4 i_4)) 4%Z) -> (∀(i_4 : Z), i_2 ≤ i_4 -> i_4 < i + i_1 + i_2 -> separated (a_5 (shift a_4 i_4)) 4%Z a_7 2147483646%Z) -> p_linked_n t (fun_updt a_5 (shift a_4 x_3) a_8) a a_4 i_2 i_3 a_8.
Admitted.
