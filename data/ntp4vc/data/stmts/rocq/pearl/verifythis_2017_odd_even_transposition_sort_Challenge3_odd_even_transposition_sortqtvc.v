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
Require Import Why3.int.Sum.
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import Why3.array.IntArraySorted.
Require Import Why3.array.Inversions.
Open Scope Z_scope.
Definition odd_sorted (a : list Z) (n : Z) := ∀(i : Z), 0%Z ≤ i -> 2%Z * i + 2%Z < n -> nth (Z.to_nat (2%Z * i + 1%Z)) a inhabitant ≤ nth (Z.to_nat (2%Z * i + 2%Z)) a inhabitant.
Definition even_sorted (a : list Z) (n : Z) := ∀(i : Z), 0%Z ≤ i -> 2%Z * i + 1%Z < n -> nth (Z.to_nat (2%Z * i)) a inhabitant ≤ nth (Z.to_nat (2%Z * i + 1%Z)) a inhabitant.
Theorem odd_even_transposition_sort'vc (a : list Z) : a ≡ₚ a ∧ (∀(is_sorted : bool) (a1 : list Z), length a1 = length a -> a ≡ₚ a1 ∧ (is_sorted = true -> sorted a1) -> (if decide (¬ is_sorted = true) then ((0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ 1%Z = 2%Z * 0%Z + 1%Z) ∧ a ≡ₚ a1 ∧ odd_sorted a1 1%Z ∧ (¬ True -> inversions a1 < inversions a1)) ∧ (∀(half_i : Z) (is_sorted1 : bool) (a2 : list Z), length a2 = length a1 -> (0%Z ≤ half_i ∧ 0%Z ≤ 2%Z * half_i + 1%Z) ∧ a ≡ₚ a2 ∧ odd_sorted a2 (2%Z * half_i + 1%Z) ∧ (if decide (is_sorted1 = true) then inversions a2 = inversions a1 else inversions a2 < inversions a1) -> (if decide (2%Z * half_i + 1%Z < Z.of_nat (length a2) - 1%Z) then let o1 : Z := 2%Z * half_i + 1%Z + 1%Z in (0%Z ≤ o1 ∧ o1 < Z.of_nat (length a2)) ∧ (0%Z ≤ 2%Z * half_i + 1%Z ∧ 2%Z * half_i + 1%Z < Z.of_nat (length a2)) ∧ (if decide (nth (Z.to_nat o1) a2 inhabitant < nth (Z.to_nat (2%Z * half_i + 1%Z)) a2 inhabitant) then let o2 : Z := 2%Z * half_i + 1%Z + 1%Z in ((0%Z ≤ 2%Z * half_i + 1%Z ∧ 2%Z * half_i + 1%Z < Z.of_nat (length a2)) ∧ 0%Z ≤ o2 ∧ o2 < Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> array_exchange a2 a3 (2%Z * half_i + 1%Z) o2 -> (0%Z ≤ Z.of_nat (length a2) - (2%Z * half_i + 1%Z) ∧ Z.of_nat (length a3) - (2%Z * half_i + 1%Z + 2%Z) < Z.of_nat (length a2) - (2%Z * half_i + 1%Z)) ∧ (0%Z ≤ half_i + 1%Z ∧ 0%Z ≤ 2%Z * half_i + 1%Z + 2%Z ∧ 2%Z * half_i + 1%Z + 2%Z = 2%Z * (half_i + 1%Z) + 1%Z) ∧ a ≡ₚ a3 ∧ odd_sorted a3 (2%Z * half_i + 1%Z + 2%Z) ∧ (if decide (false = true) then inversions a3 = inversions a1 else inversions a3 < inversions a1)) else (0%Z ≤ Z.of_nat (length a2) - (2%Z * half_i + 1%Z) ∧ Z.of_nat (length a2) - (2%Z * half_i + 1%Z + 2%Z) < Z.of_nat (length a2) - (2%Z * half_i + 1%Z)) ∧ (0%Z ≤ half_i + 1%Z ∧ 0%Z ≤ 2%Z * half_i + 1%Z + 2%Z ∧ 2%Z * half_i + 1%Z + 2%Z = 2%Z * (half_i + 1%Z) + 1%Z) ∧ a ≡ₚ a2 ∧ odd_sorted a2 (2%Z * half_i + 1%Z + 2%Z) ∧ (if decide (is_sorted1 = true) then inversions a2 = inversions a1 else inversions a2 < inversions a1)) else ((0%Z ≤ 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z = 2%Z * 0%Z) ∧ 0%Z ≤ 0%Z ∧ a ≡ₚ a2 ∧ (is_sorted1 = true -> odd_sorted a2 (Z.of_nat (length a2))) ∧ even_sorted a2 0%Z ∧ (if decide (is_sorted1 = true) then inversions a2 = inversions a1 else inversions a2 < inversions a1) ∧ (is_sorted1 = true ∨ inversions a2 < inversions a1)) ∧ (∀(half_i1 : Z) (is_sorted2 : bool) (a3 : list Z), length a3 = length a2 -> (0%Z ≤ half_i1 ∧ 0%Z ≤ 2%Z * half_i1) ∧ 0%Z ≤ 2%Z * half_i1 ∧ a ≡ₚ a3 ∧ (is_sorted2 = true -> odd_sorted a3 (Z.of_nat (length a3))) ∧ even_sorted a3 (2%Z * half_i1) ∧ (if decide (is_sorted2 = true) then inversions a3 = inversions a1 else inversions a3 < inversions a1) ∧ (is_sorted2 = true ∨ inversions a3 < inversions a1) -> (if decide (2%Z * half_i1 < Z.of_nat (length a3) - 1%Z) then let o1 : Z := 2%Z * half_i1 + 1%Z in (0%Z ≤ o1 ∧ o1 < Z.of_nat (length a3)) ∧ (0%Z ≤ 2%Z * half_i1 ∧ 2%Z * half_i1 < Z.of_nat (length a3)) ∧ (if decide (nth (Z.to_nat o1) a3 inhabitant < nth (Z.to_nat (2%Z * half_i1)) a3 inhabitant) then let o2 : Z := 2%Z * half_i1 + 1%Z in ((0%Z ≤ 2%Z * half_i1 ∧ 2%Z * half_i1 < Z.of_nat (length a3)) ∧ 0%Z ≤ o2 ∧ o2 < Z.of_nat (length a3)) ∧ (∀(a4 : list Z), length a4 = length a3 -> array_exchange a3 a4 (2%Z * half_i1) o2 -> (0%Z ≤ Z.of_nat (length a3) - 2%Z * half_i1 ∧ Z.of_nat (length a4) - (2%Z * half_i1 + 2%Z) < Z.of_nat (length a3) - 2%Z * half_i1) ∧ (0%Z ≤ half_i1 + 1%Z ∧ 0%Z ≤ 2%Z * half_i1 + 2%Z ∧ 2%Z * half_i1 + 2%Z = 2%Z * (half_i1 + 1%Z)) ∧ 0%Z ≤ 2%Z * half_i1 + 2%Z ∧ a ≡ₚ a4 ∧ (false = true -> odd_sorted a4 (Z.of_nat (length a4))) ∧ even_sorted a4 (2%Z * half_i1 + 2%Z) ∧ (if decide (false = true) then inversions a4 = inversions a1 else inversions a4 < inversions a1) ∧ (false = true ∨ inversions a4 < inversions a1)) else (0%Z ≤ Z.of_nat (length a3) - 2%Z * half_i1 ∧ Z.of_nat (length a3) - (2%Z * half_i1 + 2%Z) < Z.of_nat (length a3) - 2%Z * half_i1) ∧ (0%Z ≤ half_i1 + 1%Z ∧ 0%Z ≤ 2%Z * half_i1 + 2%Z ∧ 2%Z * half_i1 + 2%Z = 2%Z * (half_i1 + 1%Z)) ∧ 0%Z ≤ 2%Z * half_i1 + 2%Z ∧ a ≡ₚ a3 ∧ (is_sorted2 = true -> odd_sorted a3 (Z.of_nat (length a3))) ∧ even_sorted a3 (2%Z * half_i1 + 2%Z) ∧ (if decide (is_sorted2 = true) then inversions a3 = inversions a1 else inversions a3 < inversions a1) ∧ (is_sorted2 = true ∨ inversions a3 < inversions a1)) else (0%Z ≤ (if decide (is_sorted = true) then 0%Z else 1%Z) ∧ (if decide (is_sorted2 = true) then 0%Z else 1%Z) < (if decide (is_sorted = true) then 0%Z else 1%Z) ∨ (if decide (is_sorted = true) then 0%Z else 1%Z) = (if decide (is_sorted2 = true) then 0%Z else 1%Z) ∧ 0%Z ≤ inversions a1 ∧ inversions a3 < inversions a1) ∧ a ≡ₚ a3 ∧ (is_sorted2 = true -> sorted a3))))) else sorted a1 ∧ a ≡ₚ a1)).
Admitted.
