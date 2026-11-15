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
Require Import Why3.ocaml.Exceptions.
Open Scope Z_scope.
Definition mem (x : Z) (a : list Z) (i : Z) := ∃(j : Z), (0%Z ≤ j ∧ j < i) ∧ nth (Z.to_nat j) a inhabitant = x.
Theorem unique'vc (a : list Z) : let n : Z := Z.of_nat (length a) in ∀(h : gmap Z unit), h = (∅ : gmap Z unit) -> 0%Z ≤ n ∧ (∀(res : list Z), (∀(i : Z), 0%Z ≤ i ∧ i < n -> nth (Z.to_nat i) res inhabitant = 0%Z) ∧ Z.of_nat (length res) = n -> (let o1 : Z := n - 1%Z in (0%Z ≤ o1 + 1%Z -> (0%Z ≤ 0%Z ∧ (∀(x : Z), mem x a 0%Z = (x ∈ dom h)) ∧ (∀(x : Z), mem x a 0%Z = mem x res 0%Z) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < 0%Z -> ¬ nth (Z.to_nat i) res inhabitant = nth (Z.to_nat j) res inhabitant)) ∧ (∀(len : Z) (res1 : list Z) (h1 : gmap Z unit), length res1 = length res -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o1) ∧ (0%Z ≤ len ∧ len ≤ i) ∧ (∀(x : Z), mem x a i = (x ∈ dom h1)) ∧ (∀(x : Z), mem x a i = mem x res1 len) ∧ (∀(i1 : Z) (j : Z), 0%Z ≤ i1 ∧ i1 < j ∧ j < len -> ¬ nth (Z.to_nat i1) res1 inhabitant = nth (Z.to_nat j) res1 inhabitant) -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (if decide (¬ nth (Z.to_nat i) a inhabitant ∈ dom h1) then (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (∀(h2 : gmap Z unit), h2 = <[nth (Z.to_nat i) a inhabitant := ()]>h1 -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o2 : Z := nth (Z.to_nat i) a inhabitant in (0%Z ≤ len ∧ len < Z.of_nat (length res1)) ∧ (length (set_list res1 (Z.to_nat len) o2) = length res1 -> nth_i (set_list res1 (Z.to_nat len) o2) = fun_updt (nth_i res1) len o2 -> (0%Z ≤ len + 1%Z ∧ len + 1%Z ≤ i + 1%Z) ∧ (∀(x : Z), mem x a (i + 1%Z) = (x ∈ dom h2)) ∧ (∀(x : Z), mem x a (i + 1%Z) = mem x (set_list res1 (Z.to_nat len) o2) (len + 1%Z)) ∧ (∀(i1 : Z) (j : Z), 0%Z ≤ i1 ∧ i1 < j ∧ j < len + 1%Z -> ¬ nth (Z.to_nat i1) (set_list res1 (Z.to_nat len) o2) inhabitant = nth (Z.to_nat j) (set_list res1 (Z.to_nat len) o2) inhabitant)))) else (0%Z ≤ len ∧ len ≤ i + 1%Z) ∧ (∀(x : Z), mem x a (i + 1%Z) = (x ∈ dom h1)) ∧ (∀(x : Z), mem x a (i + 1%Z) = mem x res1 len) ∧ (∀(i1 : Z) (j : Z), 0%Z ≤ i1 ∧ i1 < j ∧ j < len -> ¬ nth (Z.to_nat i1) res1 inhabitant = nth (Z.to_nat j) res1 inhabitant))) ∧ ((0%Z ≤ len ∧ len ≤ o1 + 1%Z) ∧ (∀(x : Z), mem x a (o1 + 1%Z) = (x ∈ dom h1)) ∧ (∀(x : Z), mem x a (o1 + 1%Z) = mem x res1 len) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < len -> ¬ nth (Z.to_nat i) res1 inhabitant = nth (Z.to_nat j) res1 inhabitant) -> (0%Z ≤ 0%Z ∧ 0%Z ≤ len ∧ 0%Z + len ≤ Z.of_nat (length res1)) ∧ (∀(result : list Z), Z.of_nat (length result) = len ∧ (∀(i : Z), 0%Z ≤ i ∧ i < len -> nth (Z.to_nat i) result inhabitant = nth (Z.to_nat (0%Z + i)) res1 inhabitant) -> (∀(x : Z), mem x result (Z.of_nat (length result)) = mem x a (Z.of_nat (length a))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length result) -> ¬ nth (Z.to_nat i) result inhabitant = nth (Z.to_nat j) result inhabitant))))) ∧ (o1 + 1%Z < 0%Z -> (0%Z ≤ 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z + 0%Z ≤ Z.of_nat (length res)) ∧ (∀(result : list Z), Z.of_nat (length result) = 0%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> nth (Z.to_nat i) result inhabitant = nth (Z.to_nat (0%Z + i)) res inhabitant) -> (∀(x : Z), mem x result (Z.of_nat (length result)) = mem x a (Z.of_nat (length a))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length result) -> ¬ nth (Z.to_nat i) result inhabitant = nth (Z.to_nat j) result inhabitant))))).
Admitted.
