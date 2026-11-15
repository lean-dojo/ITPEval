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
Theorem dll_to_bst_rec'vc (prev : t loc) (next : t loc) (s : list loc) (head : loc) (ihead : Z) (n : Z) (fact0 : dll (to_fmap prev) (to_fmap next) s head ihead (ihead + n)) : if decide (n = 0%Z) then head = (if decide (ihead + n = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + n)) s inhabitant) ∧ tree (to_fmap prev) (to_fmap next) s null (Empty : Tree.tree Z) ihead (ihead + n) ∧ dom (to_fmap prev) = dom (to_fmap prev) ∧ dom (to_fmap next) = dom (to_fmap next) ∧ (0%Z < n -> (let h : Z := height (Empty : Tree.tree Z) in Z.pow 2%Z (h - 1%Z) ≤ n ∧ n < Z.pow 2%Z h)) else ¬ 2%Z = 0%Z ∧ (let nl : Z := Z.rem n 2%Z in ((0%Z ≤ n ∧ nl < n) ∧ dll (to_fmap prev) (to_fmap next) s head ihead (ihead + nl)) ∧ (∀(next1 : t loc) (prev1 : t loc) (left1 : loc) (l : Tree.tree Z), tree (to_fmap prev1) (to_fmap next1) s left1 l ihead (ihead + nl) ∧ dom (to_fmap prev1) = dom (to_fmap prev) ∧ dom (to_fmap next1) = dom (to_fmap next) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < ihead -> lookup_gmap_total (to_fmap prev1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), ihead + nl ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap prev1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < ihead -> lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), ihead + nl ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (0%Z < nl -> (let h : Z := height l in Z.pow 2%Z (h - 1%Z) ≤ nl ∧ nl < Z.pow 2%Z h)) -> (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) ∈ dom (to_fmap prev1) ∧ (∀(prev2 : t loc), to_fmap prev2 = <[if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant := left1]>(to_fmap prev1) -> (let o1 : Z := n - nl - 1%Z in let o2 : Z := ihead + nl + 1%Z in (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) ∈ dom (to_fmap next1) ∧ (let o3 : loc := lookup_gmap_total (to_fmap next1) (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) in o3 = lookup_gmap_total (to_fmap next1) (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) -> ((0%Z ≤ n ∧ o1 < n) ∧ dll (to_fmap prev2) (to_fmap next1) s o3 o2 (o2 + o1)) ∧ (∀(next2 : t loc) (prev3 : t loc) (temp : loc) (r : Tree.tree Z), tree (to_fmap prev3) (to_fmap next2) s temp r o2 (o2 + o1) ∧ dom (to_fmap prev3) = dom (to_fmap prev2) ∧ dom (to_fmap next2) = dom (to_fmap next1) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < o2 -> lookup_gmap_total (to_fmap prev3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev2) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), o2 + o1 ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap prev3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev2) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < o2 -> lookup_gmap_total (to_fmap next2) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), o2 + o1 ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap next2) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next1) (nth (Z.to_nat i) s inhabitant)) ∧ (0%Z < o1 -> (let h : Z := height r in Z.pow 2%Z (h - 1%Z) ≤ o1 ∧ o1 < Z.pow 2%Z h)) -> (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) ∈ dom (to_fmap next2) ∧ (∀(next3 : t loc), to_fmap next3 = <[if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant := temp]>(to_fmap next2) -> (let o4 : Tree.tree Z := Node l (ihead + nl) r in (if decide (o2 + o1 = Z.of_nat (length s)) then null else nth (Z.to_nat (o2 + o1)) s inhabitant) = (if decide (ihead + n = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + n)) s inhabitant) ∧ tree (to_fmap prev3) (to_fmap next3) s (if decide (ihead + nl = Z.of_nat (length s)) then null else nth (Z.to_nat (ihead + nl)) s inhabitant) o4 ihead (ihead + n) ∧ dom (to_fmap prev3) = dom (to_fmap prev) ∧ dom (to_fmap next3) = dom (to_fmap next) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < ihead -> lookup_gmap_total (to_fmap prev3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), ihead + n ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap prev3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap prev) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < ihead -> lookup_gmap_total (to_fmap next3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (∀(i : Z), ihead + n ≤ i ∧ i < Z.of_nat (length s) -> lookup_gmap_total (to_fmap next3) (nth (Z.to_nat i) s inhabitant) = lookup_gmap_total (to_fmap next) (nth (Z.to_nat i) s inhabitant)) ∧ (0%Z < n -> (let h : Z := height o4 in Z.pow 2%Z (h - 1%Z) ≤ n ∧ n < Z.pow 2%Z h)))))))))).
Admitted.
