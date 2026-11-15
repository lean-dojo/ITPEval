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
Require Import queens_vcg.queens.S.
Open Scope Z_scope.
Theorem t'vc (a : gset Z) (o1 : gset Z) (b : gset Z) (o2 : gset Z) (c : gset Z) (fact0 : ¬ a = ∅) (fact1 : o1 = a ∖ b) (fact2 : o2 = o1 ∖ c) : o2 ⊆ a ∖ b ∖ c ∧ (∀(f : Z) (e : gset Z), e ⊆ a ∖ b ∖ c -> ¬ e = ∅ -> ¬ e = ∅ ∧ (let d : Z := gset_min e in ∀(o3 : gset Z), o3 = insert_set d c ∧ (if decide (d ∈ c) then size o3 = size c else Z.of_nat (size o3) = Z.of_nat (size c) + 1%Z) -> (∀(o4 : gset Z), (∀(i : Z), (i ∈ o4) = (0%Z ≤ i ∧ i + 1%Z ∈ o3)) -> (∀(o5 : gset Z), o5 = insert_set d b ∧ (if decide (d ∈ b) then size o5 = size b else Z.of_nat (size o5) = Z.of_nat (size b) + 1%Z) -> (∀(o6 : gset Z), (∀(i : Z), (i ∈ o6) = (1%Z ≤ i ∧ i - 1%Z ∈ o5)) -> (∀(o7 : gset Z), o7 = remove_set d a ∧ (if decide (d ∈ a) then Z.of_nat (size o7) = Z.of_nat (size a) - 1%Z else size o7 = size a) -> (0%Z ≤ Z.of_nat (size a) ∧ Z.of_nat (size o7) < Z.of_nat (size a)) ∧ (∀(o8 : Z) (o9 : gset Z), o9 = remove_set d e ∧ (if decide (d ∈ e) then Z.of_nat (size o9) = Z.of_nat (size e) - 1%Z else size o9 = size e) -> (0%Z ≤ Z.of_nat (size e) ∧ Z.of_nat (size o9) < Z.of_nat (size e)) ∧ o9 ⊆ a ∖ b ∖ c))))))).
Admitted.
