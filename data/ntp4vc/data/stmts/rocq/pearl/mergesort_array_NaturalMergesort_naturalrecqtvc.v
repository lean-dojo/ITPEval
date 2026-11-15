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
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Open Scope Z_scope.
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom le : elt -> elt -> Prop.
Axiom Refl : forall  (x : elt), le x x.
Axiom Trans : forall  (x : elt) (y : elt) (z : elt) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom Total : forall  (x : elt) (y : elt), le x y ∨ le y x.
Definition sorted_sub (a : list elt) (l : Z) (u : Z) := ∀(i1 : Z) (i2 : Z), l ≤ i1 ∧ i1 < i2 ∧ i2 < u -> le (nth (Z.to_nat i1) a inhabitant) (nth (Z.to_nat i2) a inhabitant).
Definition sorted (a : list elt) := ∀(i1 : Z) (i2 : Z), 0%Z ≤ i1 ∧ i1 < i2 ∧ i2 < Z.of_nat (length a) -> le (nth (Z.to_nat i1) a inhabitant) (nth (Z.to_nat i2) a inhabitant).
Theorem naturalrec'vc (lo : Z) (a : list elt) (tmp : list elt) (k : Z) (fact0 : 0%Z ≤ lo) (fact1 : lo ≤ Z.of_nat (length a)) (fact2 : length a = length tmp) (fact3 : 0%Z ≤ k) : let n : Z := Z.of_nat (length a) in if decide (n - 1%Z ≤ lo) then (n = Z.of_nat (length a) ∨ lo + k < n ∧ n < Z.of_nat (length a)) ∧ sorted_sub a lo n ∧ permut_sub' a a (Z.to_nat lo) (length a) else (0%Z ≤ lo ∧ lo < Z.of_nat (length a)) ∧ (∀(o1 : Z), (lo < o1 ∧ o1 ≤ Z.of_nat (length a)) ∧ sorted_sub a lo o1 ∧ (o1 < Z.of_nat (length a) -> ¬ le (nth (Z.to_nat (o1 - 1%Z)) a inhabitant) (nth (Z.to_nat o1) a inhabitant)) -> (if decide (o1 = n) then (n = Z.of_nat (length a) ∨ lo + k < n ∧ n < Z.of_nat (length a)) ∧ sorted_sub a lo n ∧ permut_sub' a a (Z.to_nat lo) (length a) else let o2 : Z := k - 1%Z in (0%Z ≤ o2 + 1%Z -> ((lo + 0%Z < o1 ∧ o1 < n) ∧ sorted_sub a lo o1 ∧ permut_sub' a a (Z.to_nat lo) (length a)) ∧ (∀(mid : Z) (a1 : list elt) (tmp1 : list elt), length a1 = length a -> length tmp1 = length tmp -> (∀(i : Z), (0%Z ≤ i ∧ i ≤ o2) ∧ (lo + i < mid ∧ mid < n) ∧ sorted_sub a1 lo mid ∧ permut_sub' a a1 (Z.to_nat lo) (length a1) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < lo -> nth (Z.to_nat j) a1 inhabitant = nth (Z.to_nat j) a inhabitant) -> ((0%Z ≤ k ∧ i < k) ∧ (0%Z ≤ mid ∧ mid ≤ Z.of_nat (length a1) ∧ length a1 = length tmp1) ∧ 0%Z ≤ i) ∧ (∀(a2 : list elt) (tmp2 : list elt), length a2 = length a1 -> length tmp2 = length tmp1 -> (∀(hi : Z), (hi = Z.of_nat (length a2) ∨ mid + i < hi ∧ hi < Z.of_nat (length a2)) ∧ sorted_sub a2 mid hi ∧ permut_sub' a1 a2 (Z.to_nat mid) (length a2) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < mid -> nth (Z.to_nat j) a2 inhabitant = nth (Z.to_nat j) a1 inhabitant) -> ((0%Z ≤ lo ∧ lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ Z.of_nat (length tmp2) ∧ length tmp2 = length a2) ∧ sorted_sub a2 lo mid ∧ sorted_sub a2 mid hi) ∧ (∀(a3 : list elt), length a3 = length a2 -> sorted_sub a3 lo hi ∧ permut_sub a2 a3 (Z.to_nat lo) (Z.to_nat hi) ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < lo ∨ hi ≤ i1 ∧ i1 < Z.of_nat (length a3) -> nth (Z.to_nat i1) a3 inhabitant = nth (Z.to_nat i1) a2 inhabitant) -> (if decide (hi = n) then (n = Z.of_nat (length a3) ∨ lo + k < n ∧ n < Z.of_nat (length a3)) ∧ sorted_sub a3 lo n ∧ permut_sub' a a3 (Z.to_nat lo) (length a3) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < lo -> nth (Z.to_nat j) a3 inhabitant = nth (Z.to_nat j) a inhabitant) else (lo + (i + 1%Z) < hi ∧ hi < n) ∧ sorted_sub a3 lo hi ∧ permut_sub' a a3 (Z.to_nat lo) (length a3) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < lo -> nth (Z.to_nat j) a3 inhabitant = nth (Z.to_nat j) a inhabitant)))))) ∧ ((lo + (o2 + 1%Z) < mid ∧ mid < n) ∧ sorted_sub a1 lo mid ∧ permut_sub' a a1 (Z.to_nat lo) (length a1) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < lo -> nth (Z.to_nat j) a1 inhabitant = nth (Z.to_nat j) a inhabitant) -> (mid = Z.of_nat (length a1) ∨ lo + k < mid ∧ mid < Z.of_nat (length a1)) ∧ sorted_sub a1 lo mid ∧ permut_sub' a a1 (Z.to_nat lo) (length a1) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < lo -> nth (Z.to_nat j) a1 inhabitant = nth (Z.to_nat j) a inhabitant)))) ∧ (o2 + 1%Z < 0%Z -> (o1 = Z.of_nat (length a) ∨ lo + k < o1 ∧ o1 < Z.of_nat (length a)) ∧ sorted_sub a lo o1 ∧ permut_sub' a a (Z.to_nat lo) (length a)))).
Admitted.
