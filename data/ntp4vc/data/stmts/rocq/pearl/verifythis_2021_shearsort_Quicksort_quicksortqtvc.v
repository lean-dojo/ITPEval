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
Require Import Why3.why3.Ref.Ref.
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import Why3.array.IntArraySorted.
Open Scope Z_scope.
Definition qs_partition (a1 : list Z) (a2 : list Z) (l : Z) (m : Z) (r : Z) (v : Z) := permut_sub' a1 a2 (Z.to_nat l) (Z.to_nat r) ∧ (∀(j : Z), l ≤ j ∧ j < m -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), m < j ∧ j < r -> v ≤ nth (Z.to_nat j) a2 inhabitant) ∧ nth (Z.to_nat m) a2 inhabitant = v.
Theorem quicksort'vc (a : list Z) : let o1 : Z := Z.of_nat (length a) in (0%Z ≤ 0%Z ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length a)) ∧ (∀(a1 : list Z), length a1 = length a -> sorted_sub1 a1 0%Z o1 ∧ permut_sub' a a1 0%nat (Z.to_nat o1) -> sorted a1 ∧ a ≡ₚ a1).
Admitted.
