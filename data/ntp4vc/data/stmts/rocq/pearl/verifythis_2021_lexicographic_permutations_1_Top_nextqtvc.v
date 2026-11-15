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
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom permutation : Type.
Axiom permutation_inhabited : Inhabited permutation.
Global Existing Instance permutation_inhabited.
Axiom permutation_countable : Countable permutation.
Global Existing Instance permutation_countable.
Definition lt (p : list Z) (q : list Z) := (length p = length q ∧ 0%Z < Z.of_nat (length q)) ∧ (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length p)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i -> nth (Z.to_nat j) p inhabitant = nth (Z.to_nat j) q inhabitant) ∧ nth (Z.to_nat i) p inhabitant < nth (Z.to_nat i) q inhabitant).
Axiom iseq : forall {α : Type} `{Inhabited α}, α -> list α -> Z -> bool.
Axiom iseq'def : forall  {α : Type} `{Inhabited α} (x : α) (s : list α) (i : Z), (iseq x s i = true) = (nth (Z.to_nat i) s inhabitant = x).
Definition occ {α : Type} `{Inhabited α} (x : α) (s : list α) (l : Z) (u : Z) : Z := numof (iseq x s) l u.
Definition occ_all {α : Type} `{Inhabited α} (x : α) (s : list α) : Z := occ x s 0%Z (Z.of_nat (length s)).
Definition is_permutation_of (p : list Z) (a : list Z) := length p = length a ∧ (∀(x : Z), occ_all x p = occ_all x a).
Definition descending (s : list Z) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ (∀(i : Z) (j : Z), lo ≤ i ∧ i ≤ j ∧ j < hi -> nth (Z.to_nat j) s inhabitant ≤ nth (Z.to_nat i) s inhabitant).
Definition ascending (s : list Z) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ (∀(i : Z) (j : Z), lo ≤ i ∧ i ≤ j ∧ j < hi -> nth (Z.to_nat i) s inhabitant ≤ nth (Z.to_nat j) s inhabitant).
Axiom to_seq : list Z -> list Z.
Axiom to_seq'spec'0 : forall  (a : list Z), length (to_seq a) = length a.
Axiom to_seq'spec : forall  (i : Z) (a : list Z) (fact0 : 0%Z ≤ i) (fact1 : i < Z.of_nat (length (to_seq a))), nth (Z.to_nat i) (to_seq a) inhabitant = nth (Z.to_nat i) a inhabitant.
Theorem next'vc (a : list Z) (a0 : list Z) (fact0 : length a = length a0) (fact1 : is_permutation_of (to_seq a) a0) : let n : Z := Z.of_nat (length a) in let o1 : Z := n - 1%Z in ((- 1%Z ≤ o1 ∧ o1 < n) ∧ (o1 = - 1%Z ∧ n = 0%Z ∨ 0%Z ≤ o1 ∧ descending (to_seq a) o1 n)) ∧ (∀(i : Z), (- 1%Z ≤ i ∧ i < n) ∧ (i = - 1%Z ∧ n = 0%Z ∨ 0%Z ≤ i ∧ descending (to_seq a) i n) -> (0%Z < i -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o2 : Z := i - 1%Z in 0%Z ≤ o2 ∧ o2 < Z.of_nat (length a))) ∧ (∀(o2 : bool), (if decide (0%Z < i) then o2 = (if decide (nth (Z.to_nat i) a inhabitant ≤ nth (Z.to_nat (i - 1%Z)) a inhabitant) then true else false) else o2 = false) -> (if decide (o2 = true) then (0%Z ≤ i ∧ i - 1%Z < i) ∧ (- 1%Z ≤ i - 1%Z ∧ i - 1%Z < n) ∧ (i - 1%Z = - 1%Z ∧ n = 0%Z ∨ 0%Z ≤ i - 1%Z ∧ descending (to_seq a) (i - 1%Z) n) else if decide (i ≤ 0%Z) then is_permutation_of (to_seq a) a0 ∧ (∀(p : list Z), is_permutation_of p a0 -> ¬ lt (to_seq a) p) else let i0 : Z := i - 1%Z in (0%Z ≤ i0 ∧ i0 < Z.of_nat (length a)) ∧ (let x : Z := nth (Z.to_nat i0) a inhabitant in let o3 : Z := n - 1%Z in ((i ≤ o3 ∧ o3 < n) ∧ (∀(k : Z), o3 < k ∧ k < n -> nth (Z.to_nat k) a inhabitant ≤ x)) ∧ (∀(j : Z), (i ≤ j ∧ j < n) ∧ (∀(k : Z), j < k ∧ k < n -> nth (Z.to_nat k) a inhabitant ≤ x) -> (let o4 : Z := i - 1%Z in (0%Z ≤ o4 ∧ o4 < Z.of_nat (length a)) ∧ (0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (if decide (nth (Z.to_nat j) a inhabitant ≤ nth (Z.to_nat o4) a inhabitant) then (0%Z ≤ j ∧ j - 1%Z < j) ∧ (i ≤ j - 1%Z ∧ j - 1%Z < n) ∧ (∀(k : Z), j - 1%Z < k ∧ k < n -> nth (Z.to_nat k) a inhabitant ≤ x) else (0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (let z : Z := nth (Z.to_nat j) a inhabitant in let o5 : Z := i - 1%Z in ((0%Z ≤ o5 ∧ o5 < Z.of_nat (length a)) ∧ 0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (∀(a1 : list Z), length a1 = length a -> nth (Z.to_nat o5) a1 inhabitant = nth (Z.to_nat j) a inhabitant ∧ nth (Z.to_nat j) a1 inhabitant = nth (Z.to_nat o5) a inhabitant ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a1) -> ¬ k = o5 -> ¬ k = j -> nth (Z.to_nat k) a1 inhabitant = nth (Z.to_nat k) a inhabitant) ∧ is_permutation_of (to_seq a1) (to_seq a) -> ((i0 < i ∧ i0 < n - 1%Z ∧ n - 1%Z < n) ∧ is_permutation_of (to_seq a1) a0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i0 -> nth (Z.to_nat k) a1 inhabitant = nth (Z.to_nat k) a inhabitant) ∧ nth (Z.to_nat i0) a1 inhabitant = z ∧ i - i0 = n - (n - 1%Z) ∧ (∀(k : Z), 0%Z < k ∧ k < i - i0 -> nth (Z.to_nat (i0 + k)) a1 inhabitant = nth (Z.to_nat (n - k)) a1 inhabitant ∧ nth (Z.to_nat (n - k)) a1 inhabitant = nth (Z.to_nat (i0 + k)) a1 inhabitant)) ∧ (∀(j1 : Z) (i1 : Z) (a2 : list Z), length a2 = length a1 -> (i0 < i1 ∧ i0 < j1 ∧ j1 < n) ∧ is_permutation_of (to_seq a2) a0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i0 -> nth (Z.to_nat k) a2 inhabitant = nth (Z.to_nat k) a inhabitant) ∧ nth (Z.to_nat i0) a2 inhabitant = z ∧ i1 - i0 = n - j1 ∧ (∀(k : Z), i1 ≤ k ∧ k ≤ j1 -> nth (Z.to_nat k) a2 inhabitant = nth (Z.to_nat k) a1 inhabitant) ∧ (∀(k : Z), 0%Z < k ∧ k < i1 - i0 -> nth (Z.to_nat (i0 + k)) a2 inhabitant = nth (Z.to_nat (n - k)) a1 inhabitant ∧ nth (Z.to_nat (n - k)) a2 inhabitant = nth (Z.to_nat (i0 + k)) a1 inhabitant) -> (if decide (i1 < j1) then ((0%Z ≤ i1 ∧ i1 < Z.of_nat (length a2)) ∧ 0%Z ≤ j1 ∧ j1 < Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> nth (Z.to_nat i1) a3 inhabitant = nth (Z.to_nat j1) a2 inhabitant ∧ nth (Z.to_nat j1) a3 inhabitant = nth (Z.to_nat i1) a2 inhabitant ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length a3) -> ¬ k = i1 -> ¬ k = j1 -> nth (Z.to_nat k) a3 inhabitant = nth (Z.to_nat k) a2 inhabitant) ∧ is_permutation_of (to_seq a3) (to_seq a2) -> (0%Z ≤ j1 - i1 ∧ j1 - 1%Z - (i1 + 1%Z) < j1 - i1) ∧ (i0 < i1 + 1%Z ∧ i0 < j1 - 1%Z ∧ j1 - 1%Z < n) ∧ is_permutation_of (to_seq a3) a0 ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i0 -> nth (Z.to_nat k) a3 inhabitant = nth (Z.to_nat k) a inhabitant) ∧ nth (Z.to_nat i0) a3 inhabitant = z ∧ i1 + 1%Z - i0 = n - (j1 - 1%Z) ∧ (∀(k : Z), i1 + 1%Z ≤ k ∧ k ≤ j1 - 1%Z -> nth (Z.to_nat k) a3 inhabitant = nth (Z.to_nat k) a1 inhabitant) ∧ (∀(k : Z), 0%Z < k ∧ k < i1 + 1%Z - i0 -> nth (Z.to_nat (i0 + k)) a3 inhabitant = nth (Z.to_nat (n - k)) a1 inhabitant ∧ nth (Z.to_nat (n - k)) a3 inhabitant = nth (Z.to_nat (i0 + k)) a1 inhabitant)) else (∀(p : list Z), is_permutation_of p a0 ∧ lt (to_seq a) p ∧ lt p (to_seq a2) -> (let a11 : list Z := to_seq a in let v : Z := nth (Z.to_nat i0) p inhabitant in if decide (v = x) then let o6 : Z := n - 1%Z in let o7 : Z := i0 + 1%Z in (o7 ≤ o6 + 1%Z -> (∀(k : Z), i0 + 1%Z ≤ k ∧ k < o7 -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a11 inhabitant) ∧ (∀(l : Z), (o7 ≤ l ∧ l ≤ o6) ∧ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < l -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a11 inhabitant) -> nth (Z.to_nat l) p inhabitant = nth (Z.to_nat l) a11 inhabitant ∧ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < l + 1%Z -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a11 inhabitant)) ∧ ¬ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < o6 + 1%Z -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a11 inhabitant)) ∧ ¬ o6 + 1%Z < o7 else v = z ∧ (let a21 : list Z := to_seq a2 in length a21 = length a2 ∧ (∀(i2 : Z), 0%Z ≤ i2 ∧ i2 < Z.of_nat (length a21) -> nth (Z.to_nat i2) a21 inhabitant = nth (Z.to_nat i2) a2 inhabitant) -> (let o6 : Z := n - 1%Z in let o7 : Z := i0 + 1%Z in (o7 ≤ o6 + 1%Z -> (∀(k : Z), i0 + 1%Z ≤ k ∧ k < o7 -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a21 inhabitant) ∧ (∀(l : Z), (o7 ≤ l ∧ l ≤ o6) ∧ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < l -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a21 inhabitant) -> nth (Z.to_nat l) p inhabitant = nth (Z.to_nat l) a21 inhabitant ∧ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < l + 1%Z -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a21 inhabitant)) ∧ ¬ (∀(k : Z), i0 + 1%Z ≤ k ∧ k < o6 + 1%Z -> nth (Z.to_nat k) p inhabitant = nth (Z.to_nat k) a21 inhabitant)) ∧ ¬ o6 + 1%Z < o7)))) ∧ ((∀(p : list Z), ¬ (is_permutation_of p a0 ∧ lt (to_seq a) p ∧ lt p (to_seq a2))) -> is_permutation_of (to_seq a2) a0 ∧ lt (to_seq a) (to_seq a2) ∧ (∀(p : list Z), is_permutation_of p a0 -> ¬ (lt (to_seq a) p ∧ lt p (to_seq a2))))))))))))))).
Admitted.
