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
Require Import contiki_list.A_Index_of_item.A_Index_of_item.
Open Scope Z_scope.
Theorem goal1 (t_1 : addr -> addr) (a : addr) (i_1 : Z) (i : Z) (i_2 : Z) (t : Z -> Z) : let a_1 : addr := t_1 (shift a i_1) in 0%Z ≤ i -> i_1 ≤ i -> i_1 < i -> i_2 ≤ i_1 -> 0%Z ≤ i_2 -> i_2 < i -> region (base a) ≤ 0%Z -> region (base a_1) ≤ 0%Z -> framed t_1 -> linked t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> (i_2 ≤ i -> valid_rw t (shift a i_2) (i - i_2)) -> (∀(i_3 : Z), i_3 < i_1 -> i_2 ≤ i_3 -> ¬ a_1 = t_1 (shift a i_3)) -> l_index_of t_1 a_1 a i_2 i = i_1.
Admitted.
