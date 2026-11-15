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
Require Import selection_sort.Axiomatic1.Axiomatic1.
Require Import selection_sort.A_Count.A_Count.
Require Import selection_sort.Compound.Compound.
Require Import selection_sort.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal0 (i_2 : Z) (i_1 : Z) (a : addr) (i : Z) (t : addr -> Z) (fact0 : i_2 ≤ i_1) (fact1 : region (base a) ≤ 0%Z) (fact2 : is_uint32 i_1) (fact3 : is_uint32 i_2) (fact4 : is_sint32 i) (fact5 : p_strictupperbound_1' t (shift a i_2) 0%Z (i_1 - i_2) i) : p_strictupperbound_1' t a i_2 i_1 i.
Admitted.
