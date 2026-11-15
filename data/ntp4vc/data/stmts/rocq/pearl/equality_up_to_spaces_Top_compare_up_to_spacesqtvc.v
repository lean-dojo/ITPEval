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
Axiom char : Type.
Axiom char_inhabited : Inhabited char.
Global Existing Instance char_inhabited.
Axiom char_countable : Countable char.
Global Existing Instance char_countable.
Axiom space : char.
Axiom eq : char -> char -> bool.
Axiom eq'spec : forall  (x : char) (y : char), (eq x y = true) = (x = y).
Axiom char_string : Type.
Axiom char_string_inhabited : Inhabited char_string.
Global Existing Instance char_string_inhabited.
Axiom char_string_countable : Countable char_string.
Global Existing Instance char_string_countable.
Axiom remove_spaces : list char -> list char.
Axiom remove_spaces'def : forall  (s : list char), if decide (Z.of_nat (length s) = 0%Z) then remove_spaces s = s else if decide (eq (nth 0%nat s inhabitant) space = true) then remove_spaces s = remove_spaces (drop 1%nat s) else remove_spaces s = cons (nth 0%nat s inhabitant) (remove_spaces (drop 1%nat s)).
Theorem compare_up_to_spaces'vc (x : list char) (y : list char) : let n : Z := Z.of_nat (length x) in let m : Z := Z.of_nat (length y) in ((0%Z ≤ 0%Z ∧ 0%Z ≤ n) ∧ (0%Z ≤ 0%Z ∧ 0%Z ≤ m) ∧ (remove_spaces x = remove_spaces y) = (remove_spaces (drop 0%nat x) = remove_spaces (drop 0%nat y))) ∧ (∀(j : Z) (i : Z), (0%Z ≤ i ∧ i ≤ n) ∧ (0%Z ≤ j ∧ j ≤ m) ∧ (remove_spaces x = remove_spaces y) = (remove_spaces (drop (Z.to_nat i) x) = remove_spaces (drop (Z.to_nat j) y)) -> (∀(o1 : bool), (if decide (i < n) then o1 = true else o1 = (if decide (j < m) then true else false)) -> (if decide (o1 = true) then ∀(o2 : bool), (if decide (i < n) then let o3 : char := space in let o4 : char := nth (Z.to_nat i) x inhabitant in o2 = eq o4 o3 ∧ (o2 = true) = (o4 = o3) else o2 = false) -> (if decide (o2 = true) then (0%Z ≤ n - i + m - j ∧ n - (i + 1%Z) + m - j < n - i + m - j) ∧ (0%Z ≤ i + 1%Z ∧ i + 1%Z ≤ n) ∧ (0%Z ≤ j ∧ j ≤ m) ∧ (remove_spaces x = remove_spaces y) = (remove_spaces (drop (Z.to_nat (i + 1%Z)) x) = remove_spaces (drop (Z.to_nat j) y)) else ∀(o3 : bool), (if decide (j < m) then let o4 : char := space in let o5 : char := nth (Z.to_nat j) y inhabitant in o3 = eq o5 o4 ∧ (o3 = true) = (o5 = o4) else o3 = false) -> (if decide (o3 = true) then (0%Z ≤ n - i + m - j ∧ n - i + m - (j + 1%Z) < n - i + m - j) ∧ (0%Z ≤ i ∧ i ≤ n) ∧ (0%Z ≤ j + 1%Z ∧ j + 1%Z ≤ m) ∧ (remove_spaces x = remove_spaces y) = (remove_spaces (drop (Z.to_nat i) x) = remove_spaces (drop (Z.to_nat (j + 1%Z)) y)) else ∀(o4 : bool), (if decide (i = n) then o4 = true else o4 = (if decide (j = m) then true else false)) -> (if decide (o4 = true) then ¬ remove_spaces x = remove_spaces y else let o5 : char := nth (Z.to_nat j) y inhabitant in let o6 : char := nth (Z.to_nat i) x inhabitant in let o7 : bool := eq o6 o5 in (o7 = true) = (o6 = o5) -> (if decide (¬ o7 = true) then ¬ remove_spaces x = remove_spaces y else (0%Z ≤ n - i + m - j ∧ n - (i + 1%Z) + m - (j + 1%Z) < n - i + m - j) ∧ (0%Z ≤ i + 1%Z ∧ i + 1%Z ≤ n) ∧ (0%Z ≤ j + 1%Z ∧ j + 1%Z ≤ m) ∧ (remove_spaces x = remove_spaces y) = (remove_spaces (drop (Z.to_nat (i + 1%Z)) x) = remove_spaces (drop (Z.to_nat (j + 1%Z)) y)))))) else remove_spaces x = remove_spaces y))).
Admitted.
