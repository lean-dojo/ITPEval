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
Require Import is_sorted.Compound.Compound.
Require Import is_sorted.Axiomatic.Axiomatic.
Open Scope Z_scope.
Theorem goal0 (i_2 : Z) (a : addr) (t : Z -> Z) (i : Z) (i_1 : Z) (p : bool) (t_1 : addr -> Z) : let x : Z := 1%Z + i_2 in let a_1 : addr := shift a i_2 in region (base a) ≤ 0%Z -> linked t -> is_uint32 i -> is_uint32 i_2 -> is_sint32 i_1 -> valid_rd t (shift a 0%Z) i -> (if decide (0%Z < i) then p = false ∧ p_weaklysorted_1' t_1 a 0%Z x ∧ (if decide (2%Z + i_2 ≤ i) then i_1 = 0%Z ∧ t_1 (shift a x) < t_1 a_1 ∧ i_2 ≤ 4294967294%Z ∧ valid_rd t a_1 1%Z ∧ valid_rd t (shift a (to_uint32 x)) 1%Z else i_1 = 1%Z) else i_1 = 1%Z) -> p_sorted_1' t_1 a 0%Z i = (¬ i_1 = 0%Z).
Admitted.
