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
Theorem to_seq'vc (a : list Z) : let o1 : Z := Z.of_nat (length a) - 1%Z in (0%Z ≤ o1 + 1%Z -> (Z.of_nat (length ([] : list Z)) = 0%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> nth (Z.to_nat i) ([] : list Z) inhabitant = nth 0%nat a inhabitant)) ∧ (∀(s : list Z), ((0%Z ≤ Z.of_nat (length s) ∧ Z.of_nat (length s) ≤ o1) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> nth (Z.to_nat i) s inhabitant = nth (length s) a inhabitant) -> (0%Z ≤ Z.of_nat (length s) ∧ Z.of_nat (length s) < Z.of_nat (length a)) ∧ (let o2 : Z := nth (length s) a inhabitant in let o3 : list Z := s ++ [o2] in Z.of_nat (length o3) = 1%Z + Z.of_nat (length s) ∧ nth (length s) o3 inhabitant = o2 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> nth (Z.to_nat i) o3 inhabitant = nth (Z.to_nat i) s inhabitant) -> Z.of_nat (length o3) = Z.of_nat (length s) + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) + 1%Z -> nth (Z.to_nat i) o3 inhabitant = nth (Z.to_nat (Z.of_nat (length s) + 1%Z)) a inhabitant))) ∧ (Z.of_nat (length s) = o1 + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < o1 + 1%Z -> nth (Z.to_nat i) s inhabitant = nth (Z.to_nat (o1 + 1%Z)) a inhabitant) -> length s = length a ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length s) -> nth (Z.to_nat i) s inhabitant = nth (Z.to_nat i) a inhabitant)))) ∧ (o1 + 1%Z < 0%Z -> (let r : list Z := ([] : list Z) in length r = length a ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length r) -> nth (Z.to_nat i) r inhabitant = nth (Z.to_nat i) a inhabitant))).
Admitted.
