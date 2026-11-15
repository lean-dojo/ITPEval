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
Require Import Why3.int.Sum.
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import Why3.array.IntArraySorted.
Open Scope Z_scope.
Axiom array_max : list Z -> Z.
Axiom array_max'spec : forall  (j : Z) (a : list Z) (fact0 : 0%Z ≤ j) (fact1 : j < Z.of_nat (length a)), nth (Z.to_nat j) a inhabitant ≤ array_max a.
Definition aux (a : Z -> Z) (m : Z) (i : Z) : Z := i * (m - a i).
Axiom aux_closure : (Z -> Z) -> Z -> Z -> Z.
Axiom aux_closure_def : forall  (y : Z -> Z) (y1 : Z) (y2 : Z), aux_closure y y1 y2 = aux y y1 y2.
Definition entropy (a : list Z) (m : Z) : Z := sum (aux_closure (nth_i a) m) 0%Z (Z.of_nat (length a)).
Theorem odd_even_sort'vc (a : list Z) (fact0 : 0%Z < Z.of_nat (length a)) : let m : Z := array_max a in (∀(j : Z), 0%Z ≤ j ∧ j < Z.of_nat (length a) -> nth (Z.to_nat j) a inhabitant ≤ m) -> a ≡ₚ a ∧ (∀(ok : bool) (a1 : list Z), length a1 = length a -> a ≡ₚ a1 ∧ (ok = true -> sorted a1) -> (if decide (¬ ok = true) then (a ≡ₚ a1 ∧ (0%Z ≤ 1%Z ∧ 1%Z ≤ Z.of_nat (length a1)) ∧ Z.Odd 1%Z ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 1%Z -> Z.Odd j -> nth (Z.to_nat j) a1 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a1 inhabitant) ∧ (¬ True -> entropy a1 m < entropy a1 m)) ∧ (∀(i : Z) (ok1 : bool) (a2 : list Z), length a2 = length a1 -> a ≡ₚ a2 ∧ (0%Z ≤ i ∧ i ≤ Z.of_nat (length a2)) ∧ Z.Odd i ∧ (ok1 = true -> entropy a2 m = entropy a1 m) ∧ (ok1 = true -> (∀(j : Z), 0%Z ≤ j ∧ j < i -> Z.Odd j -> nth (Z.to_nat j) a2 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a2 inhabitant)) ∧ (¬ ok1 = true -> entropy a2 m < entropy a1 m) -> (if decide (i < Z.of_nat (length a2) - 1%Z) then let o1 : Z := i + 1%Z in (0%Z ≤ o1 ∧ o1 < Z.of_nat (length a2)) ∧ (0%Z ≤ i ∧ i < Z.of_nat (length a2)) ∧ (if decide (nth (Z.to_nat o1) a2 inhabitant < nth (Z.to_nat i) a2 inhabitant) then let o2 : Z := i + 1%Z in (nth (Z.to_nat o2) a2 inhabitant < nth (Z.to_nat i) a2 inhabitant ∧ 0%Z ≤ i ∧ i < o2 ∧ o2 < Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> array_exchange a2 a3 i o2 ∧ entropy a3 m < entropy a2 m -> (0%Z ≤ Z.of_nat (length a2) - i ∧ Z.of_nat (length a3) - (i + 2%Z) < Z.of_nat (length a2) - i) ∧ a ≡ₚ a3 ∧ (0%Z ≤ i + 2%Z ∧ i + 2%Z ≤ Z.of_nat (length a3)) ∧ Z.Odd (i + 2%Z) ∧ (false = true -> entropy a3 m = entropy a1 m) ∧ (false = true -> (∀(j : Z), 0%Z ≤ j ∧ j < i + 2%Z -> Z.Odd j -> nth (Z.to_nat j) a3 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a3 inhabitant)) ∧ (¬ false = true -> entropy a3 m < entropy a1 m)) else (0%Z ≤ Z.of_nat (length a2) - i ∧ Z.of_nat (length a2) - (i + 2%Z) < Z.of_nat (length a2) - i) ∧ a ≡ₚ a2 ∧ (0%Z ≤ i + 2%Z ∧ i + 2%Z ≤ Z.of_nat (length a2)) ∧ Z.Odd (i + 2%Z) ∧ (ok1 = true -> entropy a2 m = entropy a1 m) ∧ (ok1 = true -> (∀(j : Z), 0%Z ≤ j ∧ j < i + 2%Z -> Z.Odd j -> nth (Z.to_nat j) a2 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a2 inhabitant)) ∧ (¬ ok1 = true -> entropy a2 m < entropy a1 m)) else (a ≡ₚ a2 ∧ (0%Z ≤ 0%Z ∧ 0%Z ≤ Z.of_nat (length a2)) ∧ Z.Even 0%Z ∧ (ok1 = true -> entropy a2 m = entropy a1 m) ∧ (ok1 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length a2) - 1%Z) ∧ Z.Odd j -> nth (Z.to_nat j) a2 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a2 inhabitant)) ∧ (ok1 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < 0%Z) ∧ Z.Even j -> nth (Z.to_nat j) a2 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a2 inhabitant)) ∧ (¬ ok1 = true -> entropy a2 m < entropy a1 m)) ∧ (∀(i1 : Z) (ok2 : bool) (a3 : list Z), length a3 = length a2 -> a ≡ₚ a3 ∧ (0%Z ≤ i1 ∧ i1 ≤ Z.of_nat (length a3)) ∧ Z.Even i1 ∧ (ok2 = true -> entropy a3 m = entropy a1 m) ∧ (ok2 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length a3) - 1%Z) ∧ Z.Odd j -> nth (Z.to_nat j) a3 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a3 inhabitant)) ∧ (ok2 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < i1) ∧ Z.Even j -> nth (Z.to_nat j) a3 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a3 inhabitant)) ∧ (¬ ok2 = true -> entropy a3 m < entropy a1 m) -> (if decide (i1 < Z.of_nat (length a3) - 1%Z) then let o1 : Z := i1 + 1%Z in (0%Z ≤ o1 ∧ o1 < Z.of_nat (length a3)) ∧ (0%Z ≤ i1 ∧ i1 < Z.of_nat (length a3)) ∧ (if decide (nth (Z.to_nat o1) a3 inhabitant < nth (Z.to_nat i1) a3 inhabitant) then let o2 : Z := i1 + 1%Z in (nth (Z.to_nat o2) a3 inhabitant < nth (Z.to_nat i1) a3 inhabitant ∧ 0%Z ≤ i1 ∧ i1 < o2 ∧ o2 < Z.of_nat (length a3)) ∧ (∀(a4 : list Z), length a4 = length a3 -> array_exchange a3 a4 i1 o2 ∧ entropy a4 m < entropy a3 m -> (0%Z ≤ Z.of_nat (length a3) - i1 ∧ Z.of_nat (length a4) - (i1 + 2%Z) < Z.of_nat (length a3) - i1) ∧ a ≡ₚ a4 ∧ (0%Z ≤ i1 + 2%Z ∧ i1 + 2%Z ≤ Z.of_nat (length a4)) ∧ Z.Even (i1 + 2%Z) ∧ (false = true -> entropy a4 m = entropy a1 m) ∧ (false = true -> (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length a4) - 1%Z) ∧ Z.Odd j -> nth (Z.to_nat j) a4 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a4 inhabitant)) ∧ (false = true -> (∀(j : Z), (0%Z ≤ j ∧ j < i1 + 2%Z) ∧ Z.Even j -> nth (Z.to_nat j) a4 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a4 inhabitant)) ∧ (¬ false = true -> entropy a4 m < entropy a1 m)) else (0%Z ≤ Z.of_nat (length a3) - i1 ∧ Z.of_nat (length a3) - (i1 + 2%Z) < Z.of_nat (length a3) - i1) ∧ a ≡ₚ a3 ∧ (0%Z ≤ i1 + 2%Z ∧ i1 + 2%Z ≤ Z.of_nat (length a3)) ∧ Z.Even (i1 + 2%Z) ∧ (ok2 = true -> entropy a3 m = entropy a1 m) ∧ (ok2 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < Z.of_nat (length a3) - 1%Z) ∧ Z.Odd j -> nth (Z.to_nat j) a3 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a3 inhabitant)) ∧ (ok2 = true -> (∀(j : Z), (0%Z ≤ j ∧ j < i1 + 2%Z) ∧ Z.Even j -> nth (Z.to_nat j) a3 inhabitant ≤ nth (Z.to_nat (j + 1%Z)) a3 inhabitant)) ∧ (¬ ok2 = true -> entropy a3 m < entropy a1 m)) else (0%Z ≤ entropy a1 m + (if decide (ok = true) then 0%Z else 1%Z) ∧ entropy a3 m + (if decide (ok2 = true) then 0%Z else 1%Z) < entropy a1 m + (if decide (ok = true) then 0%Z else 1%Z)) ∧ a ≡ₚ a3 ∧ (ok2 = true -> sorted a3))))) else sorted a1 ∧ a ≡ₚ a1)).
Admitted.
