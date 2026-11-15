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
Theorem initnext'vc (p : list char) (fact0 : 1%Z ≤ Z.of_nat (length p)) : let m : Z := Z.of_nat (length p) in 0%Z ≤ m ∧ (∀(next : list Z), (∀(i : Z), 0%Z ≤ i ∧ i < m -> nth (Z.to_nat i) next inhabitant = 0%Z) ∧ Z.of_nat (length next) = m -> (if decide (1%Z < m) then (0%Z ≤ 1%Z ∧ 1%Z < Z.of_nat (length next)) ∧ (length (set_list next 1%nat 0%Z) = length next -> nth_i (set_list next 1%nat 0%Z) = fun_updt (nth_i next) 1%Z 0%Z -> ((0%Z ≤ 0%Z ∧ 0%Z < 1%Z ∧ 1%Z ≤ m) ∧ matches1 p (1%Z - 0%Z) p 0%Z 0%Z ∧ (∀(z : Z), 0%Z + 1%Z < z ∧ z < 1%Z + 1%Z -> ¬ matches1 p (1%Z + 1%Z - z) p 0%Z z) ∧ (∀(k : Z), 0%Z < k ∧ k ≤ 1%Z -> is_next p k (nth (Z.to_nat k) (set_list next 1%nat 0%Z) inhabitant))) ∧ (∀(j : Z) (i : Z) (next1 : list Z), length next1 = length (set_list next 1%nat 0%Z) -> (0%Z ≤ j ∧ j < i ∧ i ≤ m) ∧ matches1 p (i - j) p 0%Z j ∧ (∀(z : Z), j + 1%Z < z ∧ z < i + 1%Z -> ¬ matches1 p (i + 1%Z - z) p 0%Z z) ∧ (∀(k : Z), 0%Z < k ∧ k ≤ i -> is_next p k (nth (Z.to_nat k) next1 inhabitant)) -> (if decide (i < m - 1%Z) then (0%Z ≤ j ∧ j < Z.of_nat (length p)) ∧ (0%Z ≤ i ∧ i < Z.of_nat (length p)) ∧ (if decide (nth (Z.to_nat i) p inhabitant = nth (Z.to_nat j) p inhabitant) then (0%Z ≤ i + 1%Z ∧ i + 1%Z < Z.of_nat (length next1)) ∧ (length (set_list next1 (Z.to_nat (i + 1%Z)) (j + 1%Z)) = length next1 -> nth_i (set_list next1 (Z.to_nat (i + 1%Z)) (j + 1%Z)) = fun_updt (nth_i next1) (i + 1%Z) (j + 1%Z) -> (0%Z ≤ m - i ∧ m - (i + 1%Z) < m - i ∨ m - i = m - (i + 1%Z) ∧ 0%Z ≤ j ∧ j + 1%Z < j) ∧ (0%Z ≤ j + 1%Z ∧ j + 1%Z < i + 1%Z ∧ i + 1%Z ≤ m) ∧ matches1 p (i + 1%Z - (j + 1%Z)) p 0%Z (j + 1%Z) ∧ (∀(z : Z), j + 1%Z + 1%Z < z ∧ z < i + 1%Z + 1%Z -> ¬ matches1 p (i + 1%Z + 1%Z - z) p 0%Z z) ∧ (∀(k : Z), 0%Z < k ∧ k ≤ i + 1%Z -> is_next p k (nth (Z.to_nat k) (set_list next1 (Z.to_nat (i + 1%Z)) (j + 1%Z)) inhabitant))) else if decide (j = 0%Z) then (0%Z ≤ i + 1%Z ∧ i + 1%Z < Z.of_nat (length next1)) ∧ (length (set_list next1 (Z.to_nat (i + 1%Z)) 0%Z) = length next1 -> nth_i (set_list next1 (Z.to_nat (i + 1%Z)) 0%Z) = fun_updt (nth_i next1) (i + 1%Z) 0%Z -> (0%Z ≤ m - i ∧ m - (i + 1%Z) < m - i ∨ m - i = m - (i + 1%Z) ∧ 0%Z ≤ j ∧ j < j) ∧ (0%Z ≤ j ∧ j < i + 1%Z ∧ i + 1%Z ≤ m) ∧ matches1 p (i + 1%Z - j) p 0%Z j ∧ (∀(z : Z), j + 1%Z < z ∧ z < i + 1%Z + 1%Z -> ¬ matches1 p (i + 1%Z + 1%Z - z) p 0%Z z) ∧ (∀(k : Z), 0%Z < k ∧ k ≤ i + 1%Z -> is_next p k (nth (Z.to_nat k) (set_list next1 (Z.to_nat (i + 1%Z)) 0%Z) inhabitant))) else (0%Z ≤ j ∧ j < Z.of_nat (length next1)) ∧ (0%Z ≤ m - i ∧ m - i < m - i ∨ 0%Z ≤ j ∧ nth (Z.to_nat j) next1 inhabitant < j) ∧ (0%Z ≤ nth (Z.to_nat j) next1 inhabitant ∧ nth (Z.to_nat j) next1 inhabitant < i ∧ i ≤ m) ∧ matches1 p (i - nth (Z.to_nat j) next1 inhabitant) p 0%Z (nth (Z.to_nat j) next1 inhabitant) ∧ (∀(z : Z), nth (Z.to_nat j) next1 inhabitant + 1%Z < z ∧ z < i + 1%Z -> ¬ matches1 p (i + 1%Z - z) p 0%Z z) ∧ (∀(k : Z), 0%Z < k ∧ k ≤ i -> is_next p k (nth (Z.to_nat k) next1 inhabitant))) else length next1 = length p ∧ (∀(j1 : Z), 0%Z < j1 ∧ j1 < Z.of_nat (length p) -> is_next p j1 (nth (Z.to_nat j1) next1 inhabitant))))) else length next = length p ∧ (∀(j : Z), 0%Z < j ∧ j < Z.of_nat (length p) -> is_next p j (nth (Z.to_nat j) next inhabitant)))).
Admitted.
