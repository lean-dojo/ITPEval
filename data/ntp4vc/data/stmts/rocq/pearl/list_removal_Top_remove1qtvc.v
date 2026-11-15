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
Axiom mem : Type.
Axiom mem_inhabited : Inhabited mem.
Global Existing Instance mem_inhabited.
Axiom mem_countable : Countable mem.
Global Existing Instance mem_countable.
Axiom null : loc.
Axiom head : loc.
Axiom entry : loc.
Axiom head_is_not_null : ¬ head = null.
Axiom entry_is_not_null : ¬ entry = null.
Axiom head_is_not_entry : ¬ head = entry.
Axiom list : (loc -> loc) -> loc -> Z -> loc -> Prop.
Axiom list'def : forall  (n : Z) (mem1 : loc -> loc) (x : loc) (y : loc) (fact0 : 0%Z ≤ n), if decide (n = 0%Z) then list mem1 x n y = (x = y) else list mem1 x n y = (¬ x = null ∧ list mem1 (mem1 x) (n - 1%Z) y).
Theorem remove1'vc (n1 : Z) (n2 : Z) (mem1 : loc -> loc) (fact0 : 0%Z < n1) (fact1 : 0%Z < n2) (fact2 : list mem1 head n1 entry) (fact3 : list mem1 entry n2 null) : let o1 : loc := head in ¬ o1 = null ∧ (let o2 : loc := mem1 o1 in ((0%Z < 1%Z ∧ 1%Z ≤ n1) ∧ list mem1 head 1%Z o2 ∧ ¬ o2 = null ∧ list mem1 o2 (n1 - 1%Z) entry ∧ list mem1 entry n2 null) ∧ (∀(n : Z) (curr : loc) (prev : loc), (0%Z < n ∧ n ≤ n1) ∧ list mem1 head n curr ∧ ¬ curr = null ∧ (prev = null -> n = 1%Z) ∧ (¬ prev = null -> mem1 prev = curr) ∧ (¬ prev = null -> list mem1 head (n - 1%Z) prev) ∧ list mem1 curr (n1 - n) entry ∧ list mem1 entry n2 null -> (if decide (¬ curr = entry) then ¬ curr = null ∧ (0%Z ≤ n1 - n ∧ n1 - (n + 1%Z) < n1 - n) ∧ (0%Z < n + 1%Z ∧ n + 1%Z ≤ n1) ∧ list mem1 head (n + 1%Z) (mem1 curr) ∧ ¬ mem1 curr = null ∧ (curr = null -> n + 1%Z = 1%Z) ∧ (¬ curr = null -> True) ∧ (¬ curr = null -> list mem1 head (n + 1%Z - 1%Z) curr) ∧ list mem1 (mem1 curr) (n1 - (n + 1%Z)) entry ∧ list mem1 entry n2 null else if decide (prev = null) then ¬ curr = null ∧ (let o3 : loc := head in ¬ o3 = null ∧ list (fun_updt mem1 o3 (mem1 curr)) head (n1 + n2 - 1%Z) null) else ¬ curr = null ∧ ¬ prev = null ∧ list (fun_updt mem1 prev (mem1 curr)) head (n1 + n2 - 1%Z) null))).
Admitted.
