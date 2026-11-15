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
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import Why3.random.State.
Require Import Why3.random.Random.
Open Scope Z_scope.
Theorem shuffle'vc (a : list Z) : let o1 : Z := Z.of_nat (length a) - 1%Z in (1%Z ≤ o1 + 1%Z -> a ≡ₚ a ∧ (∀(a1 : list Z), length a1 = length a -> (∀(i : Z), (1%Z ≤ i ∧ i ≤ o1) ∧ a ≡ₚ a1 -> (let o2 : Z := i + 1%Z in 0%Z < o2 ∧ (∀(o3 : Z), 0%Z ≤ o3 ∧ o3 < o2 -> ((0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ 0%Z ≤ o3 ∧ o3 < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> array_exchange a1 a2 i o3 -> a ≡ₚ a2)))))) ∧ (o1 + 1%Z < 1%Z -> a ≡ₚ a).
Admitted.
