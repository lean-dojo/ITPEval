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
Theorem natural_mergesort'vc (a : list elt) : let n : Z := Z.of_nat (length a) in if decide (n ≤ 1%Z) then sorted a ∧ a ≡ₚ a else ∀(tmp : list elt), length tmp = length a ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length tmp) -> nth (Z.to_nat i) tmp inhabitant = nth (Z.to_nat i) a inhabitant) -> (((0%Z ≤ 0%Z ∧ 0%Z ≤ n) ∧ sorted_sub a 0%Z 0%Z) ∧ a ≡ₚ a) ∧ (∀(first_run : Z) (tmp1 : list elt) (a1 : list elt), length tmp1 = length tmp -> length a1 = length a -> ((0%Z ≤ first_run ∧ first_run ≤ n) ∧ sorted_sub a1 0%Z first_run) ∧ a ≡ₚ a1 -> ((0%Z ≤ 0%Z ∧ 0%Z ≤ n) ∧ (first_run ≤ first_run ∧ first_run ≤ n) ∧ sorted_sub a1 0%Z first_run ∧ a1 ≡ₚ a1) ∧ (∀(lo : Z) (first_run1 : Z) (tmp2 : list elt) (a2 : list elt), length tmp2 = length tmp1 -> length a2 = length a1 -> (0%Z ≤ lo ∧ lo ≤ n) ∧ (first_run ≤ first_run1 ∧ first_run1 ≤ n) ∧ sorted_sub a2 0%Z first_run1 ∧ (lo = 0%Z ∨ first_run1 ≤ lo ∧ first_run < first_run1) ∧ a1 ≡ₚ a2 -> (if decide (lo < n - 1%Z) then (0%Z ≤ lo ∧ lo < Z.of_nat (length a2)) ∧ (∀(mid : Z), (lo < mid ∧ mid ≤ Z.of_nat (length a2)) ∧ sorted_sub a2 lo mid ∧ (mid < Z.of_nat (length a2) -> ¬ le (nth (Z.to_nat (mid - 1%Z)) a2 inhabitant) (nth (Z.to_nat mid) a2 inhabitant)) -> (if decide (mid = n) then if decide (lo = 0%Z) then sorted a2 ∧ a ≡ₚ a2 else (0%Z ≤ n - first_run ∧ n - first_run1 < n - first_run) ∧ ((0%Z ≤ first_run1 ∧ first_run1 ≤ n) ∧ sorted_sub a2 0%Z first_run1) ∧ a ≡ₚ a2 else (0%Z ≤ mid ∧ mid < Z.of_nat (length a2)) ∧ (∀(hi : Z), (mid < hi ∧ hi ≤ Z.of_nat (length a2)) ∧ sorted_sub a2 mid hi ∧ (hi < Z.of_nat (length a2) -> ¬ le (nth (Z.to_nat (hi - 1%Z)) a2 inhabitant) (nth (Z.to_nat hi) a2 inhabitant)) -> ((0%Z ≤ lo ∧ lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ Z.of_nat (length tmp2) ∧ length tmp2 = length a2) ∧ sorted_sub a2 lo mid ∧ sorted_sub a2 mid hi) ∧ (∀(a3 : list elt), length a3 = length a2 -> sorted_sub a3 lo hi ∧ permut_sub a2 a3 (Z.to_nat lo) (Z.to_nat hi) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < lo ∨ hi ≤ i ∧ i < Z.of_nat (length a3) -> nth (Z.to_nat i) a3 inhabitant = nth (Z.to_nat i) a2 inhabitant) -> (if decide (lo = 0%Z) then (0%Z ≤ n - lo ∧ n - hi < n - lo) ∧ (0%Z ≤ hi ∧ hi ≤ n) ∧ (first_run ≤ hi ∧ hi ≤ n) ∧ sorted_sub a3 0%Z hi ∧ (hi = 0%Z ∨ hi ≤ hi ∧ first_run < hi) ∧ a1 ≡ₚ a3 else (0%Z ≤ n - lo ∧ n - hi < n - lo) ∧ (0%Z ≤ hi ∧ hi ≤ n) ∧ (first_run ≤ first_run1 ∧ first_run1 ≤ n) ∧ sorted_sub a3 0%Z first_run1 ∧ (hi = 0%Z ∨ first_run1 ≤ hi ∧ first_run < first_run1) ∧ a1 ≡ₚ a3))))) else (0%Z ≤ n - first_run ∧ n - first_run1 < n - first_run) ∧ ((0%Z ≤ first_run1 ∧ first_run1 ≤ n) ∧ sorted_sub a2 0%Z first_run1) ∧ a ≡ₚ a2))).
Admitted.
