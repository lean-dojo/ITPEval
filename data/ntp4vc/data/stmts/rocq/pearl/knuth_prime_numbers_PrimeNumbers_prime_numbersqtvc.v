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
Definition no_prime_in (l : Z) (u : Z) := ∀(x : Z), l < x ∧ x < u -> ¬ prime x.
Definition first_primes (p : Z -> Z) (u : Z) := p 0%Z = 2%Z ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < u -> p i < p j) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < u -> prime (p i)) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < u - 1%Z -> no_prime_in (p i) (p (i + 1%Z))).
Axiom Bertrand_postulate : forall  (p : Z) (fact0 : prime p), ¬ no_prime_in p (2%Z * p).
Theorem prime_numbers'vc (m : Z) (fact0 : 2%Z ≤ m) : 0%Z ≤ m ∧ (∀(p : list Z), (∀(i : Z), 0%Z ≤ i ∧ i < m -> nth (Z.to_nat i) p inhabitant = 0%Z) ∧ Z.of_nat (length p) = m -> (0%Z ≤ 0%Z ∧ 0%Z < Z.of_nat (length p)) ∧ (length (set_list p 0%nat 2%Z) = length p -> nth_i (set_list p 0%nat 2%Z) = fun_updt (nth_i p) 0%Z 2%Z -> (0%Z ≤ 1%Z ∧ 1%Z < Z.of_nat (length (set_list p 0%nat 2%Z))) ∧ (length (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) = length (set_list p 0%nat 2%Z) -> nth_i (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) = fun_updt (nth_i (set_list p 0%nat 2%Z)) 1%Z 3%Z -> (let o1 : Z := m - 1%Z in (2%Z ≤ o1 + 1%Z -> (first_primes (nth_i (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z)) 2%Z ∧ (nth (Z.to_nat (2%Z - 1%Z)) (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) inhabitant < 5%Z ∧ 5%Z < 2%Z * nth (Z.to_nat (2%Z - 1%Z)) (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) inhabitant) ∧ Z.Odd 5%Z ∧ no_prime_in (nth (Z.to_nat (2%Z - 1%Z)) (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) inhabitant) 5%Z) ∧ (∀(n : Z) (p1 : list Z), length p1 = length (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z) -> (∀(j : Z), (2%Z ≤ j ∧ j ≤ o1) ∧ first_primes (nth_i p1) j ∧ (nth (Z.to_nat (j - 1%Z)) p1 inhabitant < n ∧ n < 2%Z * nth (Z.to_nat (j - 1%Z)) p1 inhabitant) ∧ Z.Odd n ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p1 inhabitant) n -> (∀(n1 : Z) (p2 : list Z), length p2 = length p1 -> (∀(k : Z), (1%Z ≤ k ∧ k < j) ∧ first_primes (nth_i p2) j ∧ (nth (Z.to_nat (j - 1%Z)) p2 inhabitant < n1 ∧ n1 < 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant) ∧ Z.Odd n1 ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p2 inhabitant) n1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < k -> ¬ (nth (Z.to_nat i) p2 inhabitant | n1)) -> (0%Z ≤ k ∧ k < Z.of_nat (length p2)) ∧ (let o2 : Z := nth (Z.to_nat k) p2 inhabitant in ¬ o2 = 0%Z ∧ (if decide (Z.quot n1 o2 = 0%Z) then (0%Z ≤ 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 ∧ 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - (n1 + 2%Z) < 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 ∨ 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 = 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - (n1 + 2%Z) ∧ 0%Z ≤ j - k ∧ j - 1%Z < j - k) ∧ (1%Z ≤ 1%Z ∧ 1%Z < j) ∧ first_primes (nth_i p2) j ∧ (nth (Z.to_nat (j - 1%Z)) p2 inhabitant < n1 + 2%Z ∧ n1 + 2%Z < 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant) ∧ Z.Odd (n1 + 2%Z) ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p2 inhabitant) (n1 + 2%Z) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 1%Z -> ¬ (nth (Z.to_nat i) p2 inhabitant | n1 + 2%Z)) else (0%Z ≤ k ∧ k < Z.of_nat (length p2)) ∧ (0%Z ≤ k ∧ k < Z.of_nat (length p2)) ∧ (let o3 : Z := nth (Z.to_nat k) p2 inhabitant in ¬ o3 = 0%Z ∧ (if decide (nth (Z.to_nat k) p2 inhabitant < Z.rem n1 o3) then let o4 : Z := k + 1%Z in (0%Z ≤ 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 ∧ 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 < 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant - n1 ∨ 0%Z ≤ j - k ∧ j - o4 < j - k) ∧ (1%Z ≤ o4 ∧ o4 < j) ∧ first_primes (nth_i p2) j ∧ (nth (Z.to_nat (j - 1%Z)) p2 inhabitant < n1 ∧ n1 < 2%Z * nth (Z.to_nat (j - 1%Z)) p2 inhabitant) ∧ Z.Odd n1 ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p2 inhabitant) n1 ∧ (∀(i : Z), 0%Z ≤ i ∧ i < o4 -> ¬ (nth (Z.to_nat i) p2 inhabitant | n1)) else nth (Z.to_nat (j - 1%Z)) p2 inhabitant < n1 ∧ prime n1 ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p2 inhabitant) n1)))))) ∧ ((1%Z ≤ 1%Z ∧ 1%Z < j) ∧ first_primes (nth_i p1) j ∧ (nth (Z.to_nat (j - 1%Z)) p1 inhabitant < n ∧ n < 2%Z * nth (Z.to_nat (j - 1%Z)) p1 inhabitant) ∧ Z.Odd n ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p1 inhabitant) n ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 1%Z -> ¬ (nth (Z.to_nat i) p1 inhabitant | n))) ∧ (∀(n1 : Z), nth (Z.to_nat (j - 1%Z)) p1 inhabitant < n1 ∧ prime n1 ∧ no_prime_in (nth (Z.to_nat (j - 1%Z)) p1 inhabitant) n1 -> (0%Z ≤ j ∧ j < Z.of_nat (length p1)) ∧ (length (set_list p1 (Z.to_nat j) n1) = length p1 -> nth_i (set_list p1 (Z.to_nat j) n1) = fun_updt (nth_i p1) j n1 -> first_primes (nth_i (set_list p1 (Z.to_nat j) n1)) (j + 1%Z) ∧ (nth (Z.to_nat (j + 1%Z - 1%Z)) (set_list p1 (Z.to_nat j) n1) inhabitant < n1 + 2%Z ∧ n1 + 2%Z < 2%Z * nth (Z.to_nat (j + 1%Z - 1%Z)) (set_list p1 (Z.to_nat j) n1) inhabitant) ∧ Z.Odd (n1 + 2%Z) ∧ no_prime_in (nth (Z.to_nat (j + 1%Z - 1%Z)) (set_list p1 (Z.to_nat j) n1) inhabitant) (n1 + 2%Z)))) ∧ (first_primes (nth_i p1) (o1 + 1%Z) ∧ (nth (Z.to_nat (o1 + 1%Z - 1%Z)) p1 inhabitant < n ∧ n < 2%Z * nth (Z.to_nat (o1 + 1%Z - 1%Z)) p1 inhabitant) ∧ Z.Odd n ∧ no_prime_in (nth (Z.to_nat (o1 + 1%Z - 1%Z)) p1 inhabitant) n -> Z.of_nat (length p1) = m ∧ first_primes (nth_i p1) m))) ∧ (o1 + 1%Z < 2%Z -> Z.of_nat (length (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z)) = m ∧ first_primes (nth_i (set_list (set_list p 0%nat 2%Z) 1%nat 3%Z)) m))))).
Admitted.
