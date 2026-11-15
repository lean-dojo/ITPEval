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
Require Import search_vcg.search.Path.
Open Scope Z_scope.
Theorem bfs'vc : let o1 : list state := ([] : list state) in let o2 : state := start in let o3 : list state := cons o2 o1 in Z.of_nat (length o3) = 1%Z + Z.of_nat (length o1) ∧ nth 0%nat o3 inhabitant = o2 ∧ (∀(i : Z), 0%Z < i ∧ i ≤ Z.of_nat (length o1) -> nth (Z.to_nat i) o3 inhabitant = nth (Z.to_nat (i - 1%Z)) o1 inhabitant) -> (0%Z ≤ 0%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o3) -> path start (nth (Z.to_nat i) o3 inhabitant) 0%Z) ∧ (∀(t : state), path start t 0%Z -> t ∈ o3) ∧ (∀(t : state) (n : Z), path start t n -> success t -> 0%Z ≤ n)) ∧ (∀(p : Z) (cur : list state), 0%Z ≤ p ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length cur) -> path start (nth (Z.to_nat i) cur inhabitant) p) ∧ (∀(t : state), path start t p -> t ∈ cur) ∧ (∀(t : state) (n : Z), path start t n -> success t -> p ≤ n) -> (if decide (0%Z < Z.of_nat (length cur)) then let o4 : Z := Z.of_nat (length cur) - 1%Z in (0%Z ≤ o4 + 1%Z -> ((∀(l : Z), 0%Z ≤ l ∧ l < Z.of_nat (length ([] : list state)) -> (∃(j : Z), (0%Z ≤ j ∧ j < 0%Z) ∧ move (nth (Z.to_nat j) cur inhabitant) (nth (Z.to_nat l) ([] : list state) inhabitant))) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < 0%Z -> 0%Z ≤ k ∧ k < Z.of_nat (length (moves (nth (Z.to_nat j) cur inhabitant))) -> nth (Z.to_nat k) (moves (nth (Z.to_nat j) cur inhabitant)) inhabitant ∈ ([] : list state)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> ¬ success (nth (Z.to_nat j) cur inhabitant))) ∧ (∀(nxt : list state), (∀(i : Z), (0%Z ≤ i ∧ i ≤ o4) ∧ (∀(l : Z), 0%Z ≤ l ∧ l < Z.of_nat (length nxt) -> (∃(j : Z), (0%Z ≤ j ∧ j < i) ∧ move (nth (Z.to_nat j) cur inhabitant) (nth (Z.to_nat l) nxt inhabitant))) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < i -> 0%Z ≤ k ∧ k < Z.of_nat (length (moves (nth (Z.to_nat j) cur inhabitant))) -> nth (Z.to_nat k) (moves (nth (Z.to_nat j) cur inhabitant)) inhabitant ∈ nxt) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i -> ¬ success (nth (Z.to_nat j) cur inhabitant)) -> (let s : state := nth (Z.to_nat i) cur inhabitant in if decide (success s) then path start s p else let o5 : list state := moves s in let o6 : list state := o5 ++ nxt in Z.of_nat (length o6) = Z.of_nat (length o5) + Z.of_nat (length nxt) ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < Z.of_nat (length o5) -> nth (Z.to_nat i1) o6 inhabitant = nth (Z.to_nat i1) o5 inhabitant) ∧ (∀(i1 : Z), Z.of_nat (length o5) ≤ i1 ∧ i1 < Z.of_nat (length o6) -> nth (Z.to_nat i1) o6 inhabitant = nth (Z.to_nat (i1 - Z.of_nat (length o5))) nxt inhabitant) -> (∀(l : Z), 0%Z ≤ l ∧ l < Z.of_nat (length o6) -> (∃(j : Z), (0%Z ≤ j ∧ j < i + 1%Z) ∧ move (nth (Z.to_nat j) cur inhabitant) (nth (Z.to_nat l) o6 inhabitant))) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < i + 1%Z -> 0%Z ≤ k ∧ k < Z.of_nat (length (moves (nth (Z.to_nat j) cur inhabitant))) -> nth (Z.to_nat k) (moves (nth (Z.to_nat j) cur inhabitant)) inhabitant ∈ o6) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i + 1%Z -> ¬ success (nth (Z.to_nat j) cur inhabitant)))) ∧ ((∀(l : Z), 0%Z ≤ l ∧ l < Z.of_nat (length nxt) -> (∃(j : Z), (0%Z ≤ j ∧ j < o4 + 1%Z) ∧ move (nth (Z.to_nat j) cur inhabitant) (nth (Z.to_nat l) nxt inhabitant))) ∧ (∀(j : Z) (k : Z), 0%Z ≤ j ∧ j < o4 + 1%Z -> 0%Z ≤ k ∧ k < Z.of_nat (length (moves (nth (Z.to_nat j) cur inhabitant))) -> nth (Z.to_nat k) (moves (nth (Z.to_nat j) cur inhabitant)) inhabitant ∈ nxt) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < o4 + 1%Z -> ¬ success (nth (Z.to_nat j) cur inhabitant)) -> 0%Z ≤ p + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length nxt) -> path start (nth (Z.to_nat i) nxt inhabitant) (p + 1%Z)) ∧ (∀(t : state), path start t (p + 1%Z) -> t ∈ nxt) ∧ (∀(t : state) (n : Z), path start t n -> success t -> p + 1%Z ≤ n)))) ∧ (o4 + 1%Z < 0%Z -> 0%Z ≤ p + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length ([] : list state)) -> path start (nth (Z.to_nat i) ([] : list state) inhabitant) (p + 1%Z)) ∧ (∀(t : state), path start t (p + 1%Z) -> t ∈ ([] : list state)) ∧ (∀(t : state) (n : Z), path start t n -> success t -> p + 1%Z ≤ n)) else ∀(t : state) (n : Z), success t -> ¬ path start t n)).
Admitted.
