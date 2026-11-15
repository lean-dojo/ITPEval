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
Theorem fill_next'vc (s : vertex) (t : vertex) (visited : set) (current : set) (next : set) (d : Z) (v : vertex) (acc : set) (fact0 : inv s t (to_fset visited) (to_fset current) (to_fset next) d) (fact1 : shortest_path s v d) (fact2 : ∀(x : vertex), ¬ x = v -> closure (to_fset visited) (to_fset current) (to_fset next) x) (fact3 : to_fset acc = succ v) : inv s t (to_fset visited) (to_fset current) (to_fset next) d ∧ to_fset acc ⊆ succ v ∧ succ v ∖ to_fset acc ⊆ to_fset visited ∧ (∀(x : vertex), ¬ x = v -> closure (to_fset visited) (to_fset current) (to_fset next) x) ∧ (∀(acc1 : set) (next1 : set) (visited1 : set), inv s t (to_fset visited1) (to_fset current) (to_fset next1) d ∧ to_fset acc1 ⊆ succ v ∧ succ v ∖ to_fset acc1 ⊆ to_fset visited1 ∧ (∀(x : vertex), ¬ x = v -> closure (to_fset visited1) (to_fset current) (to_fset next1) x) -> (if decide (¬ to_fset acc1 = ∅) then ¬ to_fset acc1 = ∅ ∧ (∀(acc2 : set), let w : vertex := choose1 acc1 in w ∈ to_fset acc1 ∧ to_fset acc2 = remove_set w (to_fset acc1) -> (if decide (¬ w ∈ to_fset visited1) then ∀(visited2 : set), to_fset visited2 = insert_set w (to_fset visited1) ∧ (if decide (w ∈ to_fset visited1) then size (to_fset visited2) = size (to_fset visited1) else Z.of_nat (size (to_fset visited2)) = Z.of_nat (size (to_fset visited1)) + 1%Z) -> (∀(next2 : set), to_fset next2 = insert_set w (to_fset next1) ∧ (if decide (w ∈ to_fset next1) then size (to_fset next2) = size (to_fset next1) else Z.of_nat (size (to_fset next2)) = Z.of_nat (size (to_fset next1)) + 1%Z) -> (0%Z ≤ Z.of_nat (size (to_fset acc1)) ∧ Z.of_nat (size (to_fset acc2)) < Z.of_nat (size (to_fset acc1))) ∧ inv s t (to_fset visited2) (to_fset current) (to_fset next2) d ∧ to_fset acc2 ⊆ succ v ∧ succ v ∖ to_fset acc2 ⊆ to_fset visited2 ∧ (∀(x : vertex), ¬ x = v -> closure (to_fset visited2) (to_fset current) (to_fset next2) x)) else (0%Z ≤ Z.of_nat (size (to_fset acc1)) ∧ Z.of_nat (size (to_fset acc2)) < Z.of_nat (size (to_fset acc1))) ∧ inv s t (to_fset visited1) (to_fset current) (to_fset next1) d ∧ to_fset acc2 ⊆ succ v ∧ succ v ∖ to_fset acc2 ⊆ to_fset visited1 ∧ (∀(x : vertex), ¬ x = v -> closure (to_fset visited1) (to_fset current) (to_fset next1) x))) else inv s t (to_fset visited1) (to_fset current) (to_fset next1) d ∧ succ v ⊆ to_fset visited1 ∧ (∀(x : vertex), closure (to_fset visited1) (to_fset current) (to_fset next1) x))).
Admitted.
