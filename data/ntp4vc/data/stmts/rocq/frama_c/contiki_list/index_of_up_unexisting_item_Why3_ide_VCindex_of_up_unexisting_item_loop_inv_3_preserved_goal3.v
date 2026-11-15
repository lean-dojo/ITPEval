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
Open Scope Z_scope.
Theorem goal3 (i_1 : Z) (t : addr -> addr) (a : addr) (a_1 : addr) (i_3 : Z) (i : Z) (i_2 : Z) : let x : Z := 1%Z + i_1 in l_index_of t a a_1 i_3 i = i -> i_1 ≤ i -> i_3 ≤ i -> i_1 < i -> i_2 ≤ i_1 -> i_3 ≤ i_1 -> i_3 ≤ i_2 -> 0%Z ≤ i_3 -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> is_sint32 i_3 -> is_sint32 x -> (∀(i_4 : Z), i_4 < i_1 -> i_3 ≤ i_4 -> ¬ t (shift a_1 i_4) = a) -> (∀(i_4 : Z), i_4 < i_1 -> i_3 ≤ i_4 -> l_index_of t a a_1 i_1 i = i) -> l_index_of t a a_1 x i = i.
Admitted.
