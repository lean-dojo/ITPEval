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
Axiom char : Type.
Axiom char_inhabited : Inhabited char.
Global Existing Instance char_inhabited.
Axiom char_countable : Countable char.
Global Existing Instance char_countable.
Definition matches1 (a1 : list char) (i1 : Z) (a2 : list char) (i2 : Z) (n : Z) := (0%Z ≤ i1 ∧ i1 ≤ Z.of_nat (length a1) - n) ∧ (0%Z ≤ i2 ∧ i2 ≤ Z.of_nat (length a2) - n) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> nth (Z.to_nat (i1 + i)) a1 inhabitant = nth (Z.to_nat (i2 + i)) a2 inhabitant).
Definition is_next (p : list char) (j : Z) (n : Z) := (0%Z ≤ n ∧ n < j) ∧ matches1 p (j - n) p 0%Z n ∧ (∀(z : Z), n < z ∧ z < j -> ¬ matches1 p (j - z) p 0%Z z).
Definition first_occur (p : list char) (a : list char) (r : Z) := (0%Z ≤ r ∧ r < Z.of_nat (length a) -> matches1 a r p 0%Z (Z.of_nat (length p))) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < r -> ¬ matches1 a k p 0%Z (Z.of_nat (length p))).
Theorem kmp'vc (p : list char) (a : list char) (fact0 : 1%Z ≤ Z.of_nat (length p)) : let m : Z := Z.of_nat (length p) in let n : Z := Z.of_nat (length a) in 1%Z ≤ Z.of_nat (length p) ∧ (∀(next : list Z), length next = length p ∧ (∀(j : Z), 0%Z < j ∧ j < Z.of_nat (length p) -> is_next p j (nth (Z.to_nat j) next inhabitant)) -> (((0%Z ≤ 0%Z ∧ 0%Z ≤ m) ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ n) ∧ matches1 a (0%Z - 0%Z) p 0%Z 0%Z ∧ (∀(k : Z), 0%Z ≤ k ∧ k < 0%Z - 0%Z -> ¬ matches1 a k p 0%Z m)) ∧ (∀(j : Z) (i : Z), ((0%Z ≤ j ∧ j ≤ m) ∧ j ≤ i ∧ i ≤ n) ∧ matches1 a (i - j) p 0%Z j ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i - j -> ¬ matches1 a k p 0%Z m) -> (∀(o1 : bool), (if decide (j < m) then o1 = (if decide (i < n) then true else false) else o1 = false) -> (if decide (o1 = true) then (0%Z ≤ j ∧ j < Z.of_nat (length p)) ∧ (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (if decide (nth (Z.to_nat i) a inhabitant = nth (Z.to_nat j) p inhabitant) then (0%Z ≤ n - i ∧ n - (i + 1%Z) < n - i ∨ n - i = n - (i + 1%Z) ∧ 0%Z ≤ j ∧ j + 1%Z < j) ∧ ((0%Z ≤ j + 1%Z ∧ j + 1%Z ≤ m) ∧ j + 1%Z ≤ i + 1%Z ∧ i + 1%Z ≤ n) ∧ matches1 a (i + 1%Z - (j + 1%Z)) p 0%Z (j + 1%Z) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z - (j + 1%Z) -> ¬ matches1 a k p 0%Z m) else if decide (j = 0%Z) then (0%Z ≤ n - i ∧ n - (i + 1%Z) < n - i ∨ n - i = n - (i + 1%Z) ∧ 0%Z ≤ j ∧ j < j) ∧ ((0%Z ≤ j ∧ j ≤ m) ∧ j ≤ i + 1%Z ∧ i + 1%Z ≤ n) ∧ matches1 a (i + 1%Z - j) p 0%Z j ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z - j -> ¬ matches1 a k p 0%Z m) else (0%Z ≤ j ∧ j < Z.of_nat (length next)) ∧ (0%Z ≤ n - i ∧ n - i < n - i ∨ 0%Z ≤ j ∧ nth (Z.to_nat j) next inhabitant < j) ∧ ((0%Z ≤ nth (Z.to_nat j) next inhabitant ∧ nth (Z.to_nat j) next inhabitant ≤ m) ∧ nth (Z.to_nat j) next inhabitant ≤ i ∧ i ≤ n) ∧ matches1 a (i - nth (Z.to_nat j) next inhabitant) p 0%Z (nth (Z.to_nat j) next inhabitant) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i - nth (Z.to_nat j) next inhabitant -> ¬ matches1 a k p 0%Z m)) else ∀(result : Z), (if decide (j = m) then result = i - m else result = i) -> first_occur p a result)))).
Admitted.
