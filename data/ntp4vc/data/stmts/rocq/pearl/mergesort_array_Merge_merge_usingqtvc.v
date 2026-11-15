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
Theorem merge_using'vc (l : Z) (m : Z) (r : Z) (tmp : list elt) (a : list elt) (o1 : bool) (fact0 : 0%Z ≤ l) (fact1 : l ≤ m) (fact2 : m ≤ r) (fact3 : r ≤ Z.of_nat (length tmp)) (fact4 : length tmp = length a) (fact5 : sorted_sub a l m) (fact6 : sorted_sub a m r) (fact7 : if decide (l < m) then o1 = (if decide (m < r) then true else false) else o1 = false) : if decide (o1 = true) then (0%Z ≤ m ∧ m < Z.of_nat (length a)) ∧ (let o2 : Z := m - 1%Z in (0%Z ≤ o2 ∧ o2 < Z.of_nat (length a)) ∧ (if decide (le (nth (Z.to_nat o2) a inhabitant) (nth (Z.to_nat m) a inhabitant)) then sorted_sub a l r ∧ permut_sub a a (Z.to_nat l) (Z.to_nat r) else let o3 : Z := r - l in ((0%Z ≤ l ∧ 0%Z ≤ o3 ∧ l + o3 ≤ Z.of_nat (length a)) ∧ 0%Z ≤ l ∧ l + o3 ≤ Z.of_nat (length tmp)) ∧ (∀(tmp1 : list elt), length tmp1 = length tmp -> (∀(i : Z), 0%Z ≤ i ∧ i < l ∨ l + o3 ≤ i ∧ i < Z.of_nat (length tmp1) -> nth (Z.to_nat i) tmp1 inhabitant = nth (Z.to_nat i) tmp inhabitant) ∧ (∀(i : Z), l ≤ i ∧ i < l + o3 -> nth (Z.to_nat i) tmp1 inhabitant = nth (Z.to_nat (l + i - l)) a inhabitant) -> ((0%Z ≤ l ∧ l ≤ m ∧ m ≤ r ∧ r ≤ Z.of_nat (length tmp1) ∧ length tmp1 = length a) ∧ sorted_sub tmp1 l m ∧ sorted_sub tmp1 m r) ∧ (∀(a1 : list elt), length a1 = length a -> sorted_sub a1 l r ∧ permut_sub tmp1 a1 (Z.to_nat l) (Z.to_nat r) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l ∨ r ≤ i ∧ i < Z.of_nat (length a1) -> nth (Z.to_nat i) a1 inhabitant = nth (Z.to_nat i) a inhabitant) -> sorted_sub a1 l r ∧ permut_sub a a1 (Z.to_nat l) (Z.to_nat r) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l ∨ r ≤ i ∧ i < Z.of_nat (length a1) -> nth (Z.to_nat i) a1 inhabitant = nth (Z.to_nat i) a inhabitant))))) else sorted_sub a l r ∧ permut_sub a a (Z.to_nat l) (Z.to_nat r).
Admitted.
