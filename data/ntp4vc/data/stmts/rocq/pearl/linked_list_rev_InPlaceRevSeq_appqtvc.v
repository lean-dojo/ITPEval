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
Axiom result : forall {α : Type} `{Inhabited α}, list α -> Z -> α.
Axiom result'def : forall  {α : Type} `{Inhabited α} (s : list α) (i : Z), result s i = nth (Z.to_nat (Z.of_nat (length s) - 1%Z - i)) s inhabitant.
Axiom loc : Type.
Axiom loc_inhabited : Inhabited loc.
Global Existing Instance loc_inhabited.
Axiom loc_countable : Countable loc.
Global Existing Instance loc_countable.
Axiom null : loc.
Axiom eq_loc : loc -> loc -> bool.
Axiom eq_loc'spec : forall  (l1 : loc) (l2 : loc), (eq_loc l1 l2 = true) = (l1 = l2).
Definition disjoint {α : Type} `{Inhabited α} (s1 : list α) (s2 : list α) := ∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < Z.of_nat (length s1) -> (∀(i2 : Z), 0%Z ≤ i2 ∧ i2 < Z.of_nat (length s2) -> ¬ nth (Z.to_nat i1) s1 inhabitant = nth (Z.to_nat i2) s2 inhabitant).
Definition no_repet (s : list loc) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> ¬ nth (Z.to_nat i) s inhabitant ∈ drop (Z.to_nat (i + 1%Z)) s.
Axiom memory : Type -> Type.
Axiom memory_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (memory α).
Global Existing Instance memory_inhabited.
Axiom next : Type.
Axiom next_inhabited : Inhabited next.
Global Existing Instance next_inhabited.
Axiom next_countable : Countable next.
Global Existing Instance next_countable.
Definition list_seg (next1 : loc -> loc) (p : loc) (s : list loc) (q : loc) := let n : Z := Z.of_nat (length s) in (∀(i : Z), 0%Z ≤ i ∧ i < n -> ¬ nth (Z.to_nat i) s inhabitant = null) ∧ (p = q ∧ n = 0%Z ∨ 1%Z ≤ n ∧ nth 0%nat s inhabitant = p ∧ next1 (nth (Z.to_nat (n - 1%Z)) s inhabitant) = q ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n - 1%Z -> next1 (nth (Z.to_nat i) s inhabitant) = nth (Z.to_nat (i + 1%Z)) s inhabitant)).
Theorem app'vc (next1 : loc -> loc) (l1 : loc) (l1M : list loc) (l2 : loc) (l2M : list loc) (fact0 : list_seg next1 l1 l1M null) (fact1 : list_seg next1 l2 l2M null) (fact2 : disjoint l1M l2M) : let o1 : loc := null in let o2 : bool := eq_loc l1 o1 in (o2 = true) = (l1 = o1) -> (if decide (o2 = true) then list_seg next1 l2 (l1M ++ l2M) null else (¬ l1 = null ∧ list_seg next1 l1 ([] : list loc) l1 ∧ list_seg next1 l1 l1M null ∧ ([] : list loc) ++ l1M = l1M ∧ disjoint ([] : list loc) l1M) ∧ (∀(l1pM : list loc) (pM : list loc) (p : loc), ¬ p = null ∧ list_seg next1 l1 l1pM p ∧ list_seg next1 p pM null ∧ l1pM ++ pM = l1M ∧ disjoint l1pM pM -> (let o3 : loc := null in ¬ p = null ∧ (let o4 : loc := next1 p in let o5 : bool := eq_loc o4 o3 in (o5 = true) = (o4 = o3) -> (if decide (¬ o5 = true) then (0%Z ≤ 1%Z ∧ 1%Z ≤ Z.of_nat (length pM)) ∧ (let o6 : list loc := ([] : list loc) in let o7 : list loc := cons p o6 in Z.of_nat (length o7) = 1%Z + Z.of_nat (length o6) ∧ nth 0%nat o7 inhabitant = p ∧ (∀(i : Z), 0%Z < i ∧ i ≤ Z.of_nat (length o6) -> nth (Z.to_nat i) o7 inhabitant = nth (Z.to_nat (i - 1%Z)) o6 inhabitant) -> (let o8 : list loc := l1pM ++ o7 in Z.of_nat (length o8) = Z.of_nat (length l1pM) + Z.of_nat (length o7) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length l1pM) -> nth (Z.to_nat i) o8 inhabitant = nth (Z.to_nat i) l1pM inhabitant) ∧ (∀(i : Z), Z.of_nat (length l1pM) ≤ i ∧ i < Z.of_nat (length o8) -> nth (Z.to_nat i) o8 inhabitant = nth (Z.to_nat (i - Z.of_nat (length l1pM))) o7 inhabitant) -> ¬ p = null ∧ (0%Z ≤ Z.of_nat (length pM) ∧ Z.of_nat (length (drop 1%nat pM)) < Z.of_nat (length pM)) ∧ ¬ next1 p = null ∧ list_seg next1 l1 o8 (next1 p) ∧ list_seg next1 (next1 p) (drop 1%nat pM) null ∧ o8 ++ drop 1%nat pM = l1M ∧ disjoint o8 (drop 1%nat pM))) else ¬ p = null ∧ list_seg (fun_updt next1 p l2) l1 (l1M ++ l2M) null))))).
Admitted.
