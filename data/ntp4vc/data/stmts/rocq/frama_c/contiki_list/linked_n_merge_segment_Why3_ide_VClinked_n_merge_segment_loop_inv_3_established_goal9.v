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
Open Scope Z_scope.
Theorem goal9 (i_2 : Z) (i : Z) (a : addr) (a_1 : addr) (a_2 : addr) (a_3 : addr) (t_1 : addr -> addr) (t : Z -> Z) (i_1 : Z) (fact0 : ¬ i_2 = 0%Z) (fact1 : 0%Z ≤ i) (fact2 : 0%Z ≤ i_2) (fact3 : region (base a) ≤ 0%Z) (fact4 : region (base a_1) ≤ 0%Z) (fact5 : region (base a_2) ≤ 0%Z) (fact6 : region (base a_3) ≤ 0%Z) (fact7 : framed t_1) (fact8 : linked t) (fact9 : is_sint32 i) (fact10 : is_sint32 i_1) (fact11 : is_sint32 i_2) (fact12 : valid_rw t (shift a_3 0%Z) 2147483646%Z) (fact13 : p_linked_n t t_1 a a_3 i_1 i_2 a_2) (fact14 : p_linked_n t t_1 a_2 a_3 (i_1 + i_2) i a_1) : p_linked_n t t_1 a a_3 i_1 i_2 (t_1 (shift (t_1 (shift a_3 (i_1 + i_2 - 1%Z))) 0%Z)).
Admitted.
