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
Theorem bottom_up_mergesort'vc (a : list elt) : let n : Z := Z.of_nat (length a) in ∀(tmp : list elt), length tmp = length a ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length tmp) -> nth (Z.to_nat i) tmp inhabitant = nth (Z.to_nat i) a inhabitant) -> (1%Z ≤ 1%Z ∧ a ≡ₚ a ∧ (∀(k : Z), let l : Z := k * 1%Z in 0%Z ≤ l ∧ l < n -> sorted_sub a l (Z.min n (l + 1%Z)))) ∧ (∀(len : Z) (tmp1 : list elt) (a1 : list elt), length tmp1 = length tmp -> length a1 = length a -> 1%Z ≤ len ∧ a ≡ₚ a1 ∧ (∀(k : Z), let l : Z := k * len in 0%Z ≤ l ∧ l < n -> sorted_sub a1 l (Z.min n (l + len))) -> (if decide (len < n) then ((0%Z ≤ 0%Z ∧ 0%Z = 2%Z * 0%Z * len) ∧ a1 ≡ₚ a1 ∧ (∀(k : Z), let l : Z := k * len in 0%Z ≤ l ∧ l < n -> sorted_sub a1 l (Z.min n (l + len))) ∧ (∀(k : Z), let l : Z := k * (2%Z * len) in 0%Z ≤ l ∧ l < 0%Z -> sorted_sub a1 l (Z.min n (l + 2%Z * len)))) ∧ (∀(i : Z) (tmp2 : list elt) (a2 : list elt), length tmp2 = length tmp1 -> length a2 = length a1 -> 0%Z ≤ 2%Z * i * len ∧ a1 ≡ₚ a2 ∧ (∀(k : Z), let l : Z := k * len in 2%Z * i * len ≤ l ∧ l < n -> sorted_sub a2 l (Z.min n (l + len))) ∧ (∀(k : Z), let l : Z := k * (2%Z * len) in 0%Z ≤ l ∧ l < 2%Z * i * len -> sorted_sub a2 l (Z.min n (l + 2%Z * len))) -> (if decide (2%Z * i * len < n - len) then let mid : Z := 2%Z * i * len + len in let hi : Z := Z.min n (mid + len) in ((0%Z ≤ 2%Z * i * len ∧ 2%Z * i * len ≤ mid ∧ mid ≤ hi ∧ hi ≤ Z.of_nat (length tmp2) ∧ length tmp2 = length a2) ∧ sorted_sub a2 (2%Z * i * len) mid ∧ sorted_sub a2 mid hi) ∧ (∀(a3 : list elt), length a3 = length a2 -> sorted_sub a3 (2%Z * i * len) hi ∧ permut_sub a2 a3 (Z.to_nat (2%Z * i * len)) (Z.to_nat hi) ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < 2%Z * i * len ∨ hi ≤ i1 ∧ i1 < Z.of_nat (length a3) -> nth (Z.to_nat i1) a3 inhabitant = nth (Z.to_nat i1) a2 inhabitant) -> (0%Z ≤ n + len - 2%Z * i * len ∧ n + len - (mid + len) < n + len - 2%Z * i * len) ∧ (0%Z ≤ mid + len ∧ mid + len = 2%Z * (i + 1%Z) * len) ∧ a1 ≡ₚ a3 ∧ (∀(k : Z), let l : Z := k * len in mid + len ≤ l ∧ l < n -> sorted_sub a3 l (Z.min n (l + len))) ∧ (∀(k : Z), let l : Z := k * (2%Z * len) in 0%Z ≤ l ∧ l < mid + len -> sorted_sub a3 l (Z.min n (l + 2%Z * len)))) else (0%Z ≤ 2%Z * n - len ∧ 2%Z * n - 2%Z * len < 2%Z * n - len) ∧ 1%Z ≤ 2%Z * len ∧ a ≡ₚ a2 ∧ (∀(k : Z), let l : Z := k * (2%Z * len) in 0%Z ≤ l ∧ l < n -> sorted_sub a2 l (Z.min n (l + 2%Z * len))))) else sorted a1 ∧ a ≡ₚ a1)).
Admitted.
