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
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Require Import Why3.bintree.Height.
Open Scope Z_scope.
Axiom loc : Type.
Axiom loc_inhabited : Inhabited loc.
Global Existing Instance loc_inhabited.
Axiom loc_countable : Countable loc.
Global Existing Instance loc_countable.
Axiom t : Type -> Type.
Axiom t_inhabited : forall  {χ : Type} `{Inhabited χ} `{Countable χ}, Inhabited (t χ).
Global Existing Instance t_inhabited.
Axiom to_fmap : forall {χ : Type} `{Inhabited χ} `{Countable χ}, t χ -> gmap loc χ.
Axiom null : loc.
Definition valid (prev : gmap loc loc) (next : gmap loc loc) (s : list loc) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> ¬ nth (Z.to_nat i) s inhabitant = null ∧ nth (Z.to_nat i) s inhabitant ∈ dom prev ∧ nth (Z.to_nat i) s inhabitant ∈ dom next ∧ (∀(j : Z), i < j ∧ j < Z.of_nat (length s) -> ¬ nth (Z.to_nat i) s inhabitant = nth (Z.to_nat j) s inhabitant).
Definition dll (prev : gmap loc loc) (next : gmap loc loc) (s : list loc) (head : loc) (lo : Z) (hi : Z) := valid prev next s ∧ (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ head = (if decide (lo = Z.of_nat (length s)) then null else nth (Z.to_nat lo) s inhabitant) ∧ (∀(i : Z), lo ≤ i ∧ i < hi - 1%Z -> lookup_gmap_total next (nth (Z.to_nat i) s inhabitant) = nth (Z.to_nat (i + 1%Z)) s inhabitant) ∧ (∀(i : Z), lo < i ∧ i < hi -> lookup_gmap_total prev (nth (Z.to_nat i) s inhabitant) = nth (Z.to_nat (i - 1%Z)) s inhabitant) ∧ (lo < hi -> lookup_gmap_total next (nth (Z.to_nat (hi - 1%Z)) s inhabitant) = (if decide (hi = Z.of_nat (length s)) then null else nth (Z.to_nat hi) s inhabitant)) ∧ (lo < hi -> lookup_gmap_total prev (nth (Z.to_nat lo) s inhabitant) = (if decide (lo = 0%Z) then null else nth (Z.to_nat (lo - 1%Z)) s inhabitant)).
Program Fixpoint tree (prev : gmap loc loc) (next : gmap loc loc) (s : list loc) (root : loc) (t1 : Tree.tree Z) (lo : Z) (hi : Z) : Prop :=
valid prev next s ∧ (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ (match t1 with | Empty => root = null ∧ lo = hi | Node l p r => (lo ≤ p ∧ p < hi) ∧ root = nth (Z.to_nat p) s inhabitant ∧ tree prev next s (lookup_gmap_total prev root) l lo p ∧ tree prev next s (lookup_gmap_total next root) r (p + 1%Z) hi end).
Admit Obligations.
Program Fixpoint inorder (s : list loc) (t1 : Tree.tree Z) : list loc :=
match t1 with | Empty => ([] : list loc) | Node l p r => inorder s l ++ cons (nth (Z.to_nat p) s inhabitant) (inorder s r) end.
Admit Obligations.
Theorem dll_to_bst_alt'vc (prev : t loc) (next : t loc) (s : list loc) (head : loc) (fact0 : dll (to_fmap prev) (to_fmap next) s head 0%Z (Z.of_nat (length s))) : dll (to_fmap prev) (to_fmap next) s head 0%Z (Z.of_nat (length s)) ∧ (let n : Z := Z.of_nat (length s) in dll (to_fmap prev) (to_fmap next) s head 0%Z (0%Z + n) ∧ (∀(next1 : t loc) (prev1 : t loc) (o1 : loc) (o2 : Tree.tree Z), tree (to_fmap prev1) (to_fmap next1) s o1 o2 0%Z (0%Z + n) ∧ dom (to_fmap prev1) = dom (to_fmap prev) ∧ dom (to_fmap next1) = dom (to_fmap next) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> lookup_gmap_total (to_fmap prev1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z + n ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap prev1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z + n ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (0%Z < n -> (let h : Z := height o2 in Z.pow 2%Z (h - 1%Z) ≤ n ∧ n < Z.pow 2%Z h)) -> tree (to_fmap prev1) (to_fmap next1) s o1 o2 0%Z (Z.of_nat (length s)) ∧ Size.size o2 = Z.of_nat (length s) ∧ inorder s o2 = s ∧ (0%Z < Z.of_nat (length s) -> (let h : Z := height o2 in Z.pow 2%Z (h - 1%Z) ≤ Z.of_nat (length s) ∧ Z.of_nat (length s) < Z.pow 2%Z h)))).
Admitted.
