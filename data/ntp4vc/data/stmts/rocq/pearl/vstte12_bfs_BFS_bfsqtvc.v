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
Require Import vstte12_bfs_vcg.vstte12_bfs.Graph.
Open Scope Z_scope.
Axiom set : Type.
Axiom set_inhabited : Inhabited set.
Global Existing Instance set_inhabited.
Axiom set_countable : Countable set.
Global Existing Instance set_countable.
Axiom to_fset : set -> gset vertex.
Axiom choose1 : set -> vertex.
Axiom choose'spec : forall  (s : set) (fact0 : ¬ to_fset s = ∅), choose1 s ∈ to_fset s.
Definition inv (s : vertex) (t : vertex) (visited : gset vertex) (current : gset vertex) (next : gset vertex) (d : Z) := current ⊆ visited ∧ (∀(x : vertex), x ∈ current -> shortest_path s x d) ∧ next ⊆ visited ∧ (∀(x : vertex), x ∈ next -> shortest_path s x (d + 1%Z)) ∧ (∀(x : vertex) (m : Z), path s x m -> m ≤ d -> x ∈ visited) ∧ (∀(x : vertex), x ∈ visited -> (∃(m : Z), path s x m ∧ m ≤ d + 1%Z)) ∧ (∀(x : vertex), shortest_path s x (d + 1%Z) -> x ∈ next ∨ ¬ x ∈ visited) ∧ (t ∈ visited -> t ∈ current ∨ t ∈ next).
Definition closure (visited : gset vertex) (current : gset vertex) (next : gset vertex) (x : vertex) := x ∈ visited -> ¬ x ∈ current -> ¬ x ∈ next -> (∀(y : vertex), y ∈ succ x -> y ∈ visited).
Theorem bfs'vc (visited : set) (o1 : set) (o2 : set) (visited1 : set) (s : vertex) (current : set) (t : vertex) (fact0 : to_fset visited = (∅ : gset vertex)) (fact1 : Z.of_nat (size (to_fset visited)) = 0%Z) (fact2 : to_fset o1 = (∅ : gset vertex)) (fact3 : Z.of_nat (size (to_fset o1)) = 0%Z) (fact4 : to_fset o2 = (∅ : gset vertex)) (fact5 : Z.of_nat (size (to_fset o2)) = 0%Z) (fact6 : to_fset visited1 = insert_set s (to_fset visited)) (fact7 : if decide (s ∈ to_fset visited) then size (to_fset visited1) = size (to_fset visited) else Z.of_nat (size (to_fset visited1)) = Z.of_nat (size (to_fset visited)) + 1%Z) (fact8 : to_fset current = insert_set s (to_fset o1)) (fact9 : if decide (s ∈ to_fset o1) then size (to_fset current) = size (to_fset o1) else Z.of_nat (size (to_fset current)) = Z.of_nat (size (to_fset o1)) + 1%Z) : inv s t (to_fset visited1) (to_fset current) (to_fset o2) 0%Z ∧ (to_fset current = ∅ -> to_fset o2 = ∅) ∧ (∀(x : vertex), closure (to_fset visited1) (to_fset current) (to_fset o2) x) ∧ 0%Z ≤ 0%Z ∧ (∀(d : Z) (next : set) (current1 : set) (visited2 : set), inv s t (to_fset visited2) (to_fset current1) (to_fset next) d ∧ (to_fset current1 = ∅ -> to_fset next = ∅) ∧ (∀(x : vertex), closure (to_fset visited2) (to_fset current1) (to_fset next) x) ∧ 0%Z ≤ d -> (if decide (¬ to_fset current1 = ∅) then ¬ to_fset current1 = ∅ ∧ (∀(current2 : set), let v : vertex := choose1 current1 in v ∈ to_fset current1 ∧ to_fset current2 = remove_set v (to_fset current1) -> Graph.eq v t = (v = t) -> (if decide (Graph.eq v t) then shortest_path s t d else (inv s t (to_fset visited2) (to_fset current2) (to_fset next) d ∧ shortest_path s v d ∧ (∀(x : vertex), ¬ x = v -> closure (to_fset visited2) (to_fset current2) (to_fset next) x)) ∧ (∀(next1 : set) (visited3 : set), inv s t (to_fset visited3) (to_fset current2) (to_fset next1) d ∧ succ v ⊆ to_fset visited3 ∧ (∀(x : vertex), closure (to_fset visited3) (to_fset current2) (to_fset next1) x) -> (if decide (to_fset current2 = ∅) then ∀(o3 : set), to_fset o3 = (∅ : gset vertex) ∧ Z.of_nat (size (to_fset o3)) = 0%Z -> inv s t (to_fset visited3) (to_fset next1) (to_fset o3) (d + 1%Z) ∧ (to_fset next1 = ∅ -> to_fset o3 = ∅) ∧ (∀(x : vertex), closure (to_fset visited3) (to_fset next1) (to_fset o3) x) ∧ 0%Z ≤ d + 1%Z else inv s t (to_fset visited3) (to_fset current2) (to_fset next1) d ∧ (to_fset current2 = ∅ -> to_fset next1 = ∅) ∧ (∀(x : vertex), closure (to_fset visited3) (to_fset current2) (to_fset next1) x) ∧ 0%Z ≤ d)))) else ∀(d1 : Z), ¬ path s t d1)).
Admitted.
