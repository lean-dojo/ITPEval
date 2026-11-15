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
Theorem goal2 (i : Z) (i_1 : Z) (i_2 : Z) (a : addr) (a_1 : addr) (t_1 : addr -> addr) (t : Z -> Z) (fact0 : 0%Z ≤ i) (fact1 : i_1 ≤ i) (fact2 : i ≤ i_1) (fact3 : i_2 ≤ i_1) (fact4 : 0%Z ≤ i_2) (fact5 : i_2 < i) (fact6 : region (base a) ≤ 0%Z) (fact7 : region (base a_1) ≤ 0%Z) (fact8 : framed t_1) (fact9 : linked t) (fact10 : is_sint32 i) (fact11 : is_sint32 i_1) (fact12 : is_sint32 i_2) (fact13 : i_2 ≤ i -> valid_rw t (shift a_1 i_2) (i - i_2)) (fact14 : ∀(i_3 : Z), i_3 < i_1 -> i_2 ≤ i_3 -> ¬ t_1 (shift a_1 i_3) = a) : l_index_of t_1 a a_1 i_2 i_1 = i_1.
Admitted.
