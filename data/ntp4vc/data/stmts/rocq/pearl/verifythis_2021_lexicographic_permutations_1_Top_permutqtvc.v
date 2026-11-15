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
Axiom iseq : forall {α : Type} `{Inhabited α} `{Countable α}, α -> list α -> Z -> bool.
Axiom iseq'def : forall  {α : Type} `{Inhabited α} `{Countable α} (x : α) (s : list α) (i : Z), (iseq x s i = true) = (nth (Z.to_nat i) s inhabitant = x).
Definition occ {α : Type} `{Inhabited α} `{Countable α} (x : α) (s : list α) (l : Z) (u : Z) : Z := numof (iseq x s) l u.
Definition occ_all {α : Type} `{Inhabited α} `{Countable α} (x : α) (s : list α) : Z := occ x s 0%Z (Z.of_nat (length s)).
Definition is_permutation_of (p : list Z) (a : list Z) := length p = length a ∧ (∀(x : Z), occ_all x p = occ_all x a).
Definition descending (s : list Z) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ (∀(i : Z) (j : Z), lo ≤ i ∧ i ≤ j ∧ j < hi -> nth (Z.to_nat j) s inhabitant ≤ nth (Z.to_nat i) s inhabitant).
Definition ascending (s : list Z) (lo : Z) (hi : Z) := (0%Z ≤ lo ∧ lo ≤ hi ∧ hi ≤ Z.of_nat (length s)) ∧ (∀(i : Z) (j : Z), lo ≤ i ∧ i ≤ j ∧ j < hi -> nth (Z.to_nat i) s inhabitant ≤ nth (Z.to_nat j) s inhabitant).
Axiom to_seq : list Z -> list Z.
Axiom to_seq'spec'0 : forall  (a : list Z), length (to_seq a) = length a.
Axiom to_seq'spec : forall  (i : Z) (a : list Z) (fact0 : 0%Z ≤ i) (fact1 : i < Z.of_nat (length (to_seq a))), nth (Z.to_nat i) (to_seq a) inhabitant = nth (Z.to_nat i) a inhabitant.
Axiom all_permutations : list Z -> gset (list Z).
Axiom all_permutations'spec : forall  (p : list Z) (s : list Z) (fact0 : is_permutation_of p s), p ∈ all_permutations s.
Theorem permut'vc (a : list Z) : let a0 : list Z := to_seq a in length a0 = length a ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a0) -> nth (Z.to_nat i) a0 inhabitant = nth (Z.to_nat i) a inhabitant) -> (let all1 : gset (list Z) := all_permutations a0 in (∀(p : list Z), is_permutation_of p a0 -> p ∈ all1) -> (∀(a1 : list Z), length a1 = length a -> (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < Z.of_nat (length a1) -> nth (Z.to_nat i) a1 inhabitant ≤ nth (Z.to_nat j) a1 inhabitant) ∧ is_permutation_of (to_seq a1) (to_seq a) -> (let o1 : list Z := to_seq a1 in length o1 = length a1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o1) -> nth (Z.to_nat i) o1 inhabitant = nth (Z.to_nat i) a1 inhabitant) -> (let o2 : list (list Z) := ([] : list (list Z)) in let o3 : list (list Z) := o2 ++ [o1] in Z.of_nat (length o3) = 1%Z + Z.of_nat (length o2) ∧ nth (length o2) o3 inhabitant = o1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o2) -> nth (Z.to_nat i) o3 inhabitant = nth (Z.to_nat i) o2 inhabitant) -> (let o4 : list Z := to_seq a1 in length o4 = length a1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o4) -> nth (Z.to_nat i) o4 inhabitant = nth (Z.to_nat i) a1 inhabitant) -> (let o5 : list Z := to_seq a1 in length o5 = length a1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o5) -> nth (Z.to_nat i) o5 inhabitant = nth (Z.to_nat i) a1 inhabitant) -> (let o6 : gset (list Z) := ({[o5]} : gset _) in (0%Z < Z.of_nat (length o3) ∧ is_permutation_of (to_seq a1) a0 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o3) -> is_permutation_of (nth (Z.to_nat i) o3 inhabitant) a0) ∧ (o4 = nth (Z.to_nat (Z.of_nat (length o3) - 1%Z)) o3 inhabitant ∧ nth (Z.to_nat (Z.of_nat (length o3) - 1%Z)) o3 inhabitant = to_seq a1) ∧ is_permutation_of o4 a0 ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length o3) -> lt (nth (Z.to_nat i) o3 inhabitant) (nth (Z.to_nat j) o3 inhabitant)) ∧ (∀(p : list Z), is_permutation_of p a0 -> lt p o4 -> (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length o3) - 1%Z) ∧ nth (Z.to_nat i) o3 inhabitant = p)) ∧ (∀(p : list Z), (p ∈ o6) = (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length o3)) ∧ nth (Z.to_nat i) o3 inhabitant = p)) ∧ o6 ⊆ all1) ∧ (∀(sresult : gset (list Z)) (result : list (list Z)) (a2 : list Z), length a2 = length a1 -> 0%Z < Z.of_nat (length result) ∧ is_permutation_of (to_seq a2) a0 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length result) -> is_permutation_of (nth (Z.to_nat i) result inhabitant) a0) ∧ nth (Z.to_nat (Z.of_nat (length result) - 1%Z)) result inhabitant = to_seq a2 ∧ is_permutation_of (nth (Z.to_nat (Z.of_nat (length result) - 1%Z)) result inhabitant) a0 ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length result) -> lt (nth (Z.to_nat i) result inhabitant) (nth (Z.to_nat j) result inhabitant)) ∧ (∀(p : list Z), is_permutation_of p a0 -> lt p (nth (Z.to_nat (Z.of_nat (length result) - 1%Z)) result inhabitant) -> (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length result) - 1%Z) ∧ nth (Z.to_nat i) result inhabitant = p)) ∧ (∀(p : list Z), (p ∈ sresult) = (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length result)) ∧ nth (Z.to_nat i) result inhabitant = p)) ∧ sresult ⊆ all1 -> (length a2 = length a0 ∧ is_permutation_of (to_seq a2) a0) ∧ (∀(a3 : list Z), length a3 = length a2 -> (∀(o7 : bool), is_permutation_of (to_seq a3) a0 ∧ (¬ o7 = true -> (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a3) -> nth (Z.to_nat i) a3 inhabitant = nth (Z.to_nat i) a2 inhabitant)) ∧ (¬ o7 = true -> (∀(p : list Z), is_permutation_of p a0 -> ¬ lt (to_seq a3) p)) ∧ (o7 = true -> lt (to_seq a2) (to_seq a3)) ∧ (o7 = true -> (∀(p : list Z), is_permutation_of p a0 -> ¬ (lt (to_seq a2) p ∧ lt p (to_seq a3)))) -> (if decide (o7 = true) then let o8 : list Z := to_seq a3 in length o8 = length a3 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o8) -> nth (Z.to_nat i) o8 inhabitant = nth (Z.to_nat i) a3 inhabitant) -> (let o9 : list (list Z) := result ++ [o8] in Z.of_nat (length o9) = 1%Z + Z.of_nat (length result) ∧ nth (length result) o9 inhabitant = o8 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length result) -> nth (Z.to_nat i) o9 inhabitant = nth (Z.to_nat i) result inhabitant) -> (let o10 : list Z := to_seq a3 in length o10 = length a3 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o10) -> nth (Z.to_nat i) o10 inhabitant = nth (Z.to_nat i) a3 inhabitant) -> (let o11 : list Z := to_seq a3 in length o11 = length a3 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o11) -> nth (Z.to_nat i) o11 inhabitant = nth (Z.to_nat i) a3 inhabitant) -> (0%Z ≤ Z.of_nat (size all1) - Z.of_nat (size sresult) ∧ Z.of_nat (size all1) - Z.of_nat (size (insert_set o11 sresult)) < Z.of_nat (size all1) - Z.of_nat (size sresult)) ∧ 0%Z < Z.of_nat (length o9) ∧ is_permutation_of (to_seq a3) a0 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length o9) -> is_permutation_of (nth (Z.to_nat i) o9 inhabitant) a0) ∧ (o10 = nth (Z.to_nat (Z.of_nat (length o9) - 1%Z)) o9 inhabitant ∧ nth (Z.to_nat (Z.of_nat (length o9) - 1%Z)) o9 inhabitant = to_seq a3) ∧ is_permutation_of o10 a0 ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length o9) -> lt (nth (Z.to_nat i) o9 inhabitant) (nth (Z.to_nat j) o9 inhabitant)) ∧ (∀(p : list Z), is_permutation_of p a0 -> lt p o10 -> (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length o9) - 1%Z) ∧ nth (Z.to_nat i) o9 inhabitant = p)) ∧ (∀(p : list Z), (p ∈ insert_set o11 sresult) = (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length o9)) ∧ nth (Z.to_nat i) o9 inhabitant = p)) ∧ insert_set o11 sresult ⊆ all1))) else (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length result) -> is_permutation_of (nth (Z.to_nat i) result inhabitant) (to_seq a)) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length result) -> lt (nth (Z.to_nat i) result inhabitant) (nth (Z.to_nat j) result inhabitant)) ∧ (∀(p : list Z), is_permutation_of p (to_seq a) -> (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length result)) ∧ nth (Z.to_nat i) result inhabitant = p))))))))))))).
Admitted.
