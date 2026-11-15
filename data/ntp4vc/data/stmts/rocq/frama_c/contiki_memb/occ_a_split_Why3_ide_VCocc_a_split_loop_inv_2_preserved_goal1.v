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
Require Import contiki_memb.Axiomatic13.Axiomatic13.
Require Import Why3.Memory.Memory.
Require Import contiki_memb.Compound.Compound.
Require Import contiki_memb.A_OccArray.A_OccArray.
Require Import Why3.Cint.Cint.
Open Scope Z_scope.
Theorem goal1 (t : addr -> Z) (i_3 : Z) (a : addr) (i_2 : Z) (i_4 : Z) (i_1 : Z) (i : Z) : let x : Z := l_occ_a t i_3 a i_2 i_4 in let x_1 : Z := 1%Z + i_1 in x + l_occ_a t i_3 a i_4 i_1 = l_occ_a t i_3 a i_2 i_1 -> i_1 ≤ i -> i_4 ≤ i -> i_1 < i -> i_4 ≤ i_1 -> i_2 ≤ i_4 -> region (base a) ≤ 0%Z -> i_1 ≤ 2147483646%Z -> sconst t -> is_sint32 i -> is_sint32 i_1 -> is_sint32 i_2 -> is_sint32 i_3 -> is_sint32 i_4 -> is_sint32 x_1 -> x + l_occ_a t i_3 a i_4 x_1 = l_occ_a t i_3 a i_2 x_1.
Admitted.
