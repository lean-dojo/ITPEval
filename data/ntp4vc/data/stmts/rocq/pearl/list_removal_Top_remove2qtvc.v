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
Theorem remove2'vc (n1 : Z) (n2 : Z) (mem1 : loc -> loc) (fact0 : 0%Z < n1) (fact1 : 0%Z < n2) (fact2 : list mem1 head n1 entry) (fact3 : list mem1 entry n2 null) : 0%Z < 1%Z ∧ 1%Z ≤ n1 ∧ ¬ head = null ∧ list mem1 head (1%Z - 1%Z) head ∧ list mem1 (mem1 head) (n1 - 1%Z) entry ∧ list mem1 entry n2 null ∧ (∀(n : Z) (ind : loc), (0%Z < n ∧ n ≤ n1) ∧ ¬ ind = null ∧ list mem1 head (n - 1%Z) ind ∧ list mem1 (mem1 ind) (n1 - n) entry ∧ list mem1 entry n2 null -> ¬ ind = null ∧ (if decide (¬ mem1 ind = entry) then ¬ ind = null ∧ (0%Z ≤ n1 - n ∧ n1 - (n + 1%Z) < n1 - n) ∧ (0%Z < n + 1%Z ∧ n + 1%Z ≤ n1) ∧ ¬ mem1 ind = null ∧ list mem1 head (n + 1%Z - 1%Z) (mem1 ind) ∧ list mem1 (mem1 (mem1 ind)) (n1 - (n + 1%Z)) entry ∧ list mem1 entry n2 null else let o1 : loc := entry in ¬ o1 = null ∧ ¬ ind = null ∧ list (fun_updt mem1 ind (mem1 o1)) head (n1 + n2 - 1%Z) null)).
Admitted.
