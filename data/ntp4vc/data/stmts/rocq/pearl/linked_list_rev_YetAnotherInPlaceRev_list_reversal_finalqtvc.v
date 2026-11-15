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
Axiom null : loc.
Inductive mem :=
  | mem'mk : (loc -> loc) -> mem.
Axiom mem_inhabited : Inhabited mem.
Global Existing Instance mem_inhabited.
Axiom mem_countable : Countable mem.
Global Existing Instance mem_countable.
Definition next (x : mem) := match x with |  mem'mk a => a end.
Definition valid_cells (s : Z -> loc) (n : Z) := (∀(i : Z), 0%Z ≤ i ∧ i < n -> ¬ s i = null) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < n -> 0%Z ≤ j ∧ j < n -> ¬ i = j -> ¬ s i = s j).
Definition listLR (m : mem) (s : Z -> loc) (l : loc) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi) ∧ (if decide (lo = hi) then l = null else l = s lo ∧ next m (s (hi - 1%Z)) = null ∧ (∀(k : Z), lo ≤ k ∧ k < hi - 1%Z -> next m (s k) = s (k + 1%Z))).
Definition listRL (m : mem) (s : Z -> loc) (l : loc) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi) ∧ (if decide (lo = hi) then l = null else next m (s lo) = null ∧ l = s (hi - 1%Z) ∧ (∀(k : Z), lo < k ∧ k < hi -> next m (s k) = s (k - 1%Z))).
Definition frame (m1 : mem) (m2 : mem) (s : Z -> loc) (n : Z) := ∀(p : loc), (∀(i : Z), 0%Z ≤ i ∧ i < n -> ¬ p = s i) -> next m1 p = next m2 p.
Axiom is_list : mem -> loc -> (Z -> loc) -> Z -> Prop.
Axiom result : (Z -> loc) -> Z -> loc.
Axiom result'def : forall  (s : Z -> loc) (i : Z), result s i = s (i + 1%Z).
Axiom is_list'def : forall  (n : Z) (m : mem) (l : loc) (s : Z -> loc) (fact0 : 0%Z ≤ n), if decide (n = 0%Z) then is_list m l s n = (l = null) else is_list m l s n = ((let q1' : loc := s 0%Z in l = q1' ∧ ¬ q1' = null) ∧ is_list m (next m l) (result s) (n - 1%Z)).
Axiom fc : (Z -> loc) -> Z -> Z -> loc.
Axiom fc'def : forall  (s : Z -> loc) (n : Z) (i : Z), fc s n i = s (n - 1%Z - i).
Theorem list_reversal_final'vc (mem1 : loc -> loc) : let mem2 : mem := mem'mk mem1 in ∀(s : Z -> loc) (n : Z) (l : loc), 0%Z ≤ n ∧ is_list mem2 l s n -> (valid_cells s n ∧ listLR mem2 s l 0%Z n) ∧ (∀(mem3 : loc -> loc), let mem4 : mem := mem'mk mem3 in ∀(r : loc), listRL mem4 s r 0%Z n ∧ frame mem4 mem2 s n -> is_list mem4 r (fc s n) n ∧ frame mem4 mem2 s n).
Admitted.
