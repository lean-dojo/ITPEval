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
Open Scope Z_scope.
Axiom char : Type.
Axiom char_inhabited : Inhabited char.
Global Existing Instance char_inhabited.
Axiom char_countable : Countable char.
Global Existing Instance char_countable.
Axiom power : list char -> Z -> list char.
Axiom power'def : forall  (n : Z) (w : list char) (fact0 : 0%Z ≤ n), if decide (n = 0%Z) then power w n = ([] : list char) else power w n = w ++ power w (n - 1%Z).
Theorem common_factor'vc (a : list char) (b : list char) (fact0 : a ++ b = b ++ a) : let o1 : Z := Z.of_nat (length a) in (¬ o1 = 0%Z -> ¬ Z.of_nat (length b) = 0%Z -> (if decide (Z.of_nat (length a) ≤ Z.of_nat (length b)) then let o2 : Z := Z.of_nat (length a) in (0%Z ≤ o2 ∧ o2 ≤ Z.of_nat (length b)) ∧ (let c : list char := drop (Z.to_nat o2) b in b = a ++ c ∧ (b = a ++ c -> (0%Z ≤ Z.of_nat (length b) ∧ Z.of_nat (length c) < Z.of_nat (length b)) ∧ a ++ c = c ++ a)) else (0%Z ≤ Z.of_nat (length a) ∧ Z.of_nat (length b) < Z.of_nat (length a) ∨ length a = length b ∧ 0%Z ≤ Z.of_nat (length b) ∧ Z.of_nat (length a) < Z.of_nat (length b)) ∧ b ++ a = a ++ b)) ∧ (∀(w : list char) (ka : Z) (kb : Z), (if decide (o1 = 0%Z) then w = b ∧ ka = 0%Z ∧ kb = 1%Z else if decide (Z.of_nat (length b) = 0%Z) then w = a ∧ ka = 1%Z ∧ kb = 0%Z else if decide (Z.of_nat (length a) ≤ Z.of_nat (length b)) then let c : list char := drop (length a) b in b = a ++ c ∧ (∃(kb1 : Z), ((0%Z ≤ ka ∧ a = power w ka) ∧ 0%Z ≤ kb1 ∧ c = power w kb1) ∧ kb = ka + kb1) else (0%Z ≤ kb ∧ b = power w kb) ∧ 0%Z ≤ ka ∧ a = power w ka) -> (0%Z ≤ ka ∧ a = power w ka) ∧ 0%Z ≤ kb ∧ b = power w kb).
Admitted.
