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
Axiom loc : Type.
Axiom loc_inhabited : Inhabited loc.
Global Existing Instance loc_inhabited.
Axiom loc_countable : Countable loc.
Global Existing Instance loc_countable.
Axiom eq_loc : loc -> loc -> bool.
Axiom eq_loc'spec : forall  (l1 : loc) (l2 : loc), (eq_loc l1 l2 = true) = (l1 = l2).
Axiom null : loc.
Definition disjoint (l1 : list loc) (l2 : list loc) := ∀(x : loc), ¬ (x ∈ l1 ∧ x ∈ l2).
Program Fixpoint no_repet (l : list loc) : Prop :=
match l with | [] => True | cons x r => ¬ x ∈ r ∧ no_repet r end.
Admit Obligations.
Inductive list_seg : loc -> (loc -> loc) -> list loc -> loc -> Prop :=
 | list_seg_nil (p : loc) (next : loc -> loc) : list_seg p next ([] : list loc) p
 | list_seg_cons (p : loc) (next : loc -> loc) (l : list loc) (q : loc) : ¬ p = null -> list_seg (next p) next l q -> list_seg p next (cons p l) q.
Theorem app'vc (l1 : loc) (next : loc -> loc) (l1M : list loc) (l2 : loc) (l2M : list loc) (fact0 : list_seg l1 next l1M null) (fact1 : list_seg l2 next l2M null) (fact2 : disjoint l1M l2M) : let o1 : loc := null in let o2 : bool := eq_loc l1 o1 in (o2 = true) = (l1 = o1) -> (if decide (o2 = true) then list_seg l2 next (l1M ++ l2M) null else (¬ l1 = null ∧ list_seg l1 next ([] : list loc) l1 ∧ list_seg l1 next l1M null ∧ ([] : list loc) ++ l1M = l1M ∧ disjoint ([] : list loc) l1M) ∧ (∀(l1pM : list loc) (pM : list loc) (p : loc), ¬ p = null ∧ list_seg l1 next l1pM p ∧ list_seg p next pM null ∧ l1pM ++ pM = l1M ∧ disjoint l1pM pM -> (let o3 : loc := null in ¬ p = null ∧ (let o4 : loc := next p in let o5 : bool := eq_loc o4 o3 in (o5 = true) = (o4 = o3) -> (if decide (¬ o5 = true) then match pM with | [] => False | cons h t => ¬ p = null ∧ (match pM with | [] => False | cons _ f => f = t end) ∧ ¬ next p = null ∧ list_seg l1 next (l1pM ++ cons h ([] : list loc)) (next p) ∧ list_seg (next p) next t null ∧ (l1pM ++ cons h ([] : list loc)) ++ t = l1M ∧ disjoint (l1pM ++ cons h ([] : list loc)) t end else ¬ p = null ∧ list_seg l1 (fun_updt next p l2) (l1M ++ l2M) null))))).
Admitted.
