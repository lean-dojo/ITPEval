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
Require Import search_vcg.search.Path.
Open Scope Z_scope.
Theorem dfs'vc (p : Z) (m : Z) (s : state) (fact0 : 0%Z ≤ p) (fact1 : p ≤ m + 1%Z) : if decide (m < p) then ∀(t : state) (n : Z), 0%Z ≤ n ∧ n ≤ m - p -> success t -> ¬ path s t n else if decide (success s) then path s s 0%Z ∧ success s ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ m - p else let mv : list state := moves s in let o1 : Z := Z.of_nat (length mv) - 1%Z in (0%Z ≤ o1 + 1%Z -> (∀(j : Z) (t : state) (n : Z), 0%Z ≤ j ∧ j < 0%Z -> path (nth (Z.to_nat j) mv inhabitant) t n -> success t -> ¬ (0%Z ≤ n ∧ n < m - p)) ∧ (∀(i : Z), (0%Z ≤ i ∧ i ≤ o1) ∧ (∀(j : Z) (t : state) (n : Z), 0%Z ≤ j ∧ j < i -> path (nth (Z.to_nat j) mv inhabitant) t n -> success t -> ¬ (0%Z ≤ n ∧ n < m - p)) -> (let o2 : Z := p + 1%Z in let o3 : state := nth (Z.to_nat i) mv inhabitant in ((0%Z ≤ m - p ∧ m - o2 < m - p) ∧ 0%Z ≤ o2 ∧ o2 ≤ m + 1%Z) ∧ (∀(o4 : outcome), (match o4 with | NoSolution => (∀(t : state) (n : Z), 0%Z ≤ n ∧ n ≤ m - o2 -> success t -> ¬ path o3 t n) | Solution t n => path o3 t n ∧ success t ∧ 0%Z ≤ n ∧ n ≤ m - o2 end) -> (match o4 with | Solution t n => (let o5 : Z := n + 1%Z in path s t o5 ∧ success t ∧ 0%Z ≤ o5 ∧ o5 ≤ m - p) | NoSolution => (∀(j : Z) (t : state) (n : Z), 0%Z ≤ j ∧ j < i + 1%Z -> path (nth (Z.to_nat j) mv inhabitant) t n -> success t -> ¬ (0%Z ≤ n ∧ n < m - p)) end)))) ∧ ((∀(j : Z) (t : state) (n : Z), 0%Z ≤ j ∧ j < o1 + 1%Z -> path (nth (Z.to_nat j) mv inhabitant) t n -> success t -> ¬ (0%Z ≤ n ∧ n < m - p)) -> (∀(t : state) (n : Z), 0%Z ≤ n ∧ n ≤ m - p -> success t -> ¬ path s t n))) ∧ (o1 + 1%Z < 0%Z -> (∀(t : state) (n : Z), 0%Z ≤ n ∧ n ≤ m - p -> success t -> ¬ path s t n)).
Admitted.
