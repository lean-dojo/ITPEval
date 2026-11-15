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
Require Import Why3.int.NumOf.
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
Definition inside_memory (s : Z -> loc) (n : Z) (l : loc) := l = null ∨ (∃(i : Z), (0%Z ≤ i ∧ i < n) ∧ l = s i).
Definition finite_memory (m : mem) (s : Z -> loc) (n : Z) := ∀(i : Z), 0%Z ≤ i ∧ i < n -> inside_memory s n (next m (s i)).
Axiom fc : (Z -> loc) -> (loc -> Z) -> Z -> bool.
Axiom fc'def : forall  (s : Z -> loc) (idx : loc -> Z) (i : Z), (fc s idx i = true) = (0%Z < idx (s i)).
Definition seen (s : Z -> loc) (idx : loc -> Z) (lo : Z) (hi : Z) : Z := numof (fc s idx) lo hi.
Axiom o1 : loc -> Z.
Axiom o'def : forall  (p : loc), o1 p = (if decide (p = null) then 0%Z else - 1%Z).
Theorem list_reversal'vc (mem1 : loc -> loc) : let mem2 : mem := mem'mk mem1 in ∀(s : Z -> loc) (n : Z) (l : loc), 0%Z ≤ n ∧ valid_cells s n ∧ finite_memory mem2 s n ∧ inside_memory s n l -> (let o2 : loc -> Z := o1 in (inside_memory s n l ∧ inside_memory s n null ∧ finite_memory mem2 s n ∧ (0%Z = seen s o2 0%Z n ∧ 0%Z ≤ seen s o2 0%Z n) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> - 1%Z ≤ o2 (s i) ∧ o2 (s i) ≤ 0%Z) ∧ (∀(p : loc), (o2 p = 0%Z) = (p = null)) ∧ (if decide (o2 l = - 1%Z) then o2 null = 0%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < o2 (s i) -> o2 (mem1 (s i)) = o2 (s i) - 1%Z) else ∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < o2 (s i) ∧ o2 (s i) ≤ o2 l -> o2 (mem1 (s i)) = o2 (s i) - 1%Z)) ∧ (∀(idx : loc -> Z) (r : loc) (l1 : loc) (mem3 : loc -> loc), inside_memory s n l1 ∧ inside_memory s n r ∧ finite_memory (mem'mk mem3) s n ∧ 0%Z ≤ seen s idx 0%Z n ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> - 1%Z ≤ idx (s i) ∧ idx (s i) ≤ seen s idx 0%Z n) ∧ (∀(p : loc), (idx p = 0%Z) = (p = null)) ∧ (if decide (idx l1 = - 1%Z) then idx r = seen s idx 0%Z n ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < idx (s i) -> idx (mem3 (s i)) = idx (s i) - 1%Z) else ∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < idx (s i) ∧ idx (s i) ≤ idx l1 -> idx (mem3 (s i)) = idx (s i) - 1%Z) -> ¬ l1 = null -> (if decide (idx l1 = - 1%Z) then (valid_cells s n ∧ inside_memory s n l1 ∧ ¬ l1 = null ∧ idx l1 = - 1%Z ∧ 0%Z ≤ seen s idx 0%Z n) ∧ (seen s (fun_updt idx l1 (seen s idx 0%Z n + 1%Z)) 0%Z n = 1%Z + seen s idx 0%Z n -> ¬ l1 = null ∧ ¬ l1 = null ∧ (0%Z ≤ n - seen s idx 0%Z n ∧ n - (seen s idx 0%Z n + 1%Z) < n - seen s idx 0%Z n ∨ n - seen s idx 0%Z n = n - (seen s idx 0%Z n + 1%Z) ∧ 0%Z ≤ 1%Z + idx l1 ∧ 1%Z + fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (mem3 l1) < 1%Z + idx l1) ∧ inside_memory s n (mem3 l1) ∧ inside_memory s n l1 ∧ finite_memory (mem'mk (fun_updt mem3 l1 r)) s n ∧ (seen s idx 0%Z n + 1%Z = seen s (fun_updt idx l1 (seen s idx 0%Z n + 1%Z)) 0%Z n ∧ 0%Z ≤ seen s (fun_updt idx l1 (seen s idx 0%Z n + 1%Z)) 0%Z n) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> - 1%Z ≤ fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) ∧ fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) ≤ seen s idx 0%Z n + 1%Z) ∧ (∀(p : loc), (fun_updt idx l1 (seen s idx 0%Z n + 1%Z) p = 0%Z) = (p = null)) ∧ (if decide (fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (mem3 l1) = - 1%Z) then fun_updt idx l1 (seen s idx 0%Z n + 1%Z) l1 = seen s idx 0%Z n + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) -> fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (fun_updt mem3 l1 r (s i)) = fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) - 1%Z) else ∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) ∧ fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) ≤ fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (mem3 l1) -> fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (fun_updt mem3 l1 r (s i)) = fun_updt idx l1 (seen s idx 0%Z n + 1%Z) (s i) - 1%Z)) else ¬ l1 = null ∧ ¬ l1 = null ∧ (0%Z ≤ n - seen s idx 0%Z n ∧ n - seen s idx 0%Z n < n - seen s idx 0%Z n ∨ 0%Z ≤ 1%Z + idx l1 ∧ 1%Z + idx (mem3 l1) < 1%Z + idx l1) ∧ inside_memory s n (mem3 l1) ∧ inside_memory s n l1 ∧ finite_memory (mem'mk (fun_updt mem3 l1 r)) s n ∧ 0%Z ≤ seen s idx 0%Z n ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> - 1%Z ≤ idx (s i) ∧ idx (s i) ≤ seen s idx 0%Z n) ∧ (∀(p : loc), (idx p = 0%Z) = (p = null)) ∧ (if decide (idx (mem3 l1) = - 1%Z) then idx l1 = seen s idx 0%Z n ∧ (∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < idx (s i) -> idx (fun_updt mem3 l1 r (s i)) = idx (s i) - 1%Z) else ∀(i : Z), 0%Z ≤ i ∧ i < n -> 0%Z < idx (s i) ∧ idx (s i) ≤ idx (mem3 l1) -> idx (fun_updt mem3 l1 r (s i)) = idx (s i) - 1%Z)))).
Admitted.
