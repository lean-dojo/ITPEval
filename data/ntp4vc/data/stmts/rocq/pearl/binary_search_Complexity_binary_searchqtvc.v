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
Open Scope Z_scope.
Axiom log2 : Z -> Z.
Axiom log2'def : forall  (n : Z), if decide (n ≤ 1%Z) then log2 n = 0%Z else log2 n = 1%Z + log2 (Z.rem n 2%Z).
Definition f (n : Z) : Z := if decide (n = 0%Z) then 0%Z else 1%Z + log2 n.
Theorem binary_search'vc (a : list Z) (v : Z) (fact0 : ∀(i1 : Z) (i2 : Z), 0%Z ≤ i1 ∧ i1 ≤ i2 ∧ i2 < Z.of_nat (length a) -> nth (Z.to_nat i1) a inhabitant ≤ nth (Z.to_nat i2) a inhabitant) : let o1 : Z := Z.of_nat (length a) in ((0%Z ≤ 0%Z ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length a)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z ∨ o1 ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v) ∧ 0%Z - 0%Z + f (o1 - 0%Z) ≤ f (Z.of_nat (length a))) ∧ (∀(hi : Z) (lo : Z) (time : Z), (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length a)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < lo ∨ hi ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v) ∧ time - 0%Z + f (hi - lo) ≤ f (Z.of_nat (length a)) -> (if decide (lo < hi) then ¬ 2%Z = 0%Z ∧ (let mid : Z := lo + Z.rem (hi - lo) 2%Z in (0%Z ≤ mid ∧ mid < Z.of_nat (length a)) ∧ (if decide (nth (Z.to_nat mid) a inhabitant < v) then (0%Z ≤ hi - lo ∧ hi - (mid + 1%Z) < hi - lo) ∧ (0%Z ≤ mid + 1%Z ∧ mid + 1%Z ≤ hi ∧ hi ≤ Z.of_nat (length a)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < mid + 1%Z ∨ hi ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v) ∧ time + 1%Z - 0%Z + f (hi - (mid + 1%Z)) ≤ f (Z.of_nat (length a)) else (0%Z ≤ mid ∧ mid < Z.of_nat (length a)) ∧ (if decide (v < nth (Z.to_nat mid) a inhabitant) then (0%Z ≤ hi - lo ∧ mid - lo < hi - lo) ∧ (0%Z ≤ lo ∧ lo ≤ mid ∧ mid ≤ Z.of_nat (length a)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < lo ∨ mid ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v) ∧ time + 1%Z - 0%Z + f (mid - lo) ≤ f (Z.of_nat (length a)) else ((0%Z ≤ mid ∧ mid < Z.of_nat (length a)) ∧ nth (Z.to_nat mid) a inhabitant = v ∨ mid = - 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v)) ∧ time - 0%Z ≤ f (Z.of_nat (length a))))) else ((0%Z ≤ - 1%Z ∧ - 1%Z < Z.of_nat (length a)) ∧ nth (Z.to_nat (- 1%Z)) a inhabitant = v ∨ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a) -> ¬ nth (Z.to_nat i) a inhabitant = v)) ∧ time - 0%Z ≤ f (Z.of_nat (length a)))).
Admitted.
