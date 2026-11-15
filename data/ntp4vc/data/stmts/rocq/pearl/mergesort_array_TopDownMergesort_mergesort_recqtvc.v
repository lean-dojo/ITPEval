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
Theorem mergesort_rec'vc (l : Z) (r : Z) (a : list elt) (tmp : list elt) (fact0 : 0%Z ≤ l) (fact1 : l ≤ r) (fact2 : r ≤ Z.of_nat (length a)) (fact3 : length a = length tmp) : if decide (r - 1%Z ≤ l) then sorted_sub a l r ∧ permut_sub' a a (Z.to_nat l) (Z.to_nat r) else ¬ 2%Z = 0%Z ∧ (let m : Z := l + Z.rem (r - l) 2%Z in ((0%Z ≤ r - l ∧ m - l < r - l) ∧ 0%Z ≤ l ∧ l ≤ m ∧ m ≤ Z.of_nat (length a) ∧ length a = length tmp) ∧ (∀(tmp1 : list elt) (a1 : list elt), length tmp1 = length tmp -> length a1 = length a -> sorted_sub a1 l m ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat m) -> ((0%Z ≤ r - l ∧ r - m < r - l) ∧ 0%Z ≤ m ∧ m ≤ r ∧ r ≤ Z.of_nat (length a1) ∧ length a1 = length tmp1) ∧ (∀(tmp2 : list elt) (a2 : list elt), length tmp2 = length tmp1 -> length a2 = length a1 -> sorted_sub a2 m r ∧ permut_sub' a1 a2 (Z.to_nat m) (Z.to_nat r) -> ((0%Z ≤ l ∧ l ≤ m ∧ m ≤ r ∧ r ≤ Z.of_nat (length tmp2) ∧ length tmp2 = length a2) ∧ sorted_sub a2 l m ∧ sorted_sub a2 m r) ∧ (∀(a3 : list elt), length a3 = length a2 -> sorted_sub a3 l r ∧ permut_sub a2 a3 (Z.to_nat l) (Z.to_nat r) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < l ∨ r ≤ i ∧ i < Z.of_nat (length a3) -> nth (Z.to_nat i) a3 inhabitant = nth (Z.to_nat i) a2 inhabitant) -> sorted_sub a3 l r ∧ permut_sub' a a3 (Z.to_nat l) (Z.to_nat r))))).
Admitted.
