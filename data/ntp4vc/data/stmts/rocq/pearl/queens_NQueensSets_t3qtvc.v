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
Require Import queens_vcg.queens.Solution.
Open Scope Z_scope.
Theorem t3'vc (k : Z) (a : gset Z) (s : Z) (col : Z -> Z) (b : gset Z) (c : gset Z) (sol : Z -> Z -> Z) (fact0 : 0%Z ≤ k) (fact1 : k + Z.of_nat (size a) = n) (fact2 : 0%Z ≤ s) (fact3 : ∀(i : Z), (i ∈ a) = ((0%Z ≤ i ∧ i < n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < k -> ¬ col j = i))) (fact4 : ∀(i : Z), 0%Z ≤ i -> (¬ i ∈ b) = (∀(j : Z), 0%Z ≤ j ∧ j < k -> ¬ col j = i + j - k)) (fact5 : ∀(i : Z), 0%Z ≤ i -> (¬ i ∈ c) = (∀(j : Z), 0%Z ≤ j ∧ j < k -> ¬ col j = i + k - j)) (fact6 : partial_solution k col) : if decide (¬ a = ∅) then ∀(o1 : gset Z), o1 = a ∖ b -> (∀(o2 : gset Z), o2 = o1 ∖ c -> (((0%Z = s - s ∧ 0%Z ≤ s - s) ∧ o2 ⊆ a ∖ b ∖ c ∧ partial_solution k col ∧ sorted sol s s ∧ (∀(i : Z) (j : Z), i ∈ o2 ∖ o2 -> j ∈ o2 -> i < j)) ∧ (∀(i : Z), s ≤ i ∧ i < s -> partial_solution n (sol i) ∧ eq_prefix col (sol i) k ∧ sol i k ∈ o2 ∖ o2) ∧ (∀(t : Z -> Z), partial_solution n t ∧ eq_prefix col t k ∧ t k ∈ o2 ∖ o2 -> t k ∈ o2 ∧ ¬ t k ∈ o2 ∧ (∃(i : Z), (s ≤ i ∧ i < s) ∧ eq_prefix t (sol i) n)) ∧ eq_prefix col col k ∧ eq_prefix sol sol s) ∧ (∀(e : gset Z) (s1 : Z) (sol1 : Z -> Z -> Z) (col1 : Z -> Z), (0%Z ≤ s1 - s ∧ e ⊆ a ∖ b ∖ c ∧ partial_solution k col1 ∧ sorted sol1 s s1 ∧ (∀(i : Z) (j : Z), i ∈ o2 ∖ e -> j ∈ e -> i < j)) ∧ (∀(i : Z), s ≤ i ∧ i < s1 -> partial_solution n (sol1 i) ∧ eq_prefix col1 (sol1 i) k ∧ sol1 i k ∈ o2 ∖ e) ∧ (∀(t : Z -> Z), partial_solution n t ∧ eq_prefix col1 t k ∧ t k ∈ o2 ∖ e -> t k ∈ o2 ∧ ¬ t k ∈ e ∧ (∃(i : Z), (s ≤ i ∧ i < s1) ∧ eq_prefix t (sol1 i) n)) ∧ eq_prefix col col1 k ∧ eq_prefix sol sol1 s -> (if decide (¬ e = ∅) then ¬ e = ∅ ∧ (let d : Z := gset_min e in ∀(o3 : gset Z), o3 = insert_set d c ∧ (if decide (d ∈ c) then size o3 = size c else Z.of_nat (size o3) = Z.of_nat (size c) + 1%Z) -> (∀(o4 : gset Z), (∀(i : Z), (i ∈ o4) = (0%Z ≤ i ∧ i + 1%Z ∈ o3)) -> (∀(o5 : gset Z), o5 = insert_set d b ∧ (if decide (d ∈ b) then size o5 = size b else Z.of_nat (size o5) = Z.of_nat (size b) + 1%Z) -> (∀(o6 : gset Z), (∀(i : Z), (i ∈ o6) = (1%Z ≤ i ∧ i - 1%Z ∈ o5)) -> (∀(o7 : gset Z), o7 = remove_set d a ∧ (if decide (d ∈ a) then Z.of_nat (size o7) = Z.of_nat (size a) - 1%Z else size o7 = size a) -> ((0%Z ≤ Z.of_nat (size a) ∧ Z.of_nat (size o7) < Z.of_nat (size a)) ∧ 0%Z ≤ k + 1%Z ∧ k + 1%Z + Z.of_nat (size o7) = n ∧ 0%Z ≤ s1 ∧ (∀(i : Z), (i ∈ o7) = ((0%Z ≤ i ∧ i < n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < k + 1%Z -> ¬ fun_updt col1 k d j = i))) ∧ (∀(i : Z), 0%Z ≤ i -> (¬ i ∈ o6) = (∀(j : Z), 0%Z ≤ j ∧ j < k + 1%Z -> ¬ fun_updt col1 k d j = i + j - (k + 1%Z))) ∧ (∀(i : Z), 0%Z ≤ i -> (¬ i ∈ o4) = (∀(j : Z), 0%Z ≤ j ∧ j < k + 1%Z -> ¬ fun_updt col1 k d j = i + (k + 1%Z) - j)) ∧ partial_solution (k + 1%Z) (fun_updt col1 k d)) ∧ (∀(s2 : Z) (sol2 : Z -> Z -> Z) (col2 : Z -> Z), 0%Z ≤ s2 - s1 ∧ sorted sol2 s1 s2 ∧ (∀(t : Z -> Z), (partial_solution n t ∧ eq_prefix col2 t (k + 1%Z)) = (∃(i : Z), (s1 ≤ i ∧ i < s2) ∧ eq_prefix t (sol2 i) n)) ∧ eq_prefix (fun_updt col1 k d) col2 (k + 1%Z) ∧ eq_prefix sol1 sol2 s1 -> (∀(o8 : gset Z), o8 = remove_set d e ∧ (if decide (d ∈ e) then Z.of_nat (size o8) = Z.of_nat (size e) - 1%Z else size o8 = size e) -> (0%Z ≤ Z.of_nat (size e) ∧ Z.of_nat (size o8) < Z.of_nat (size e)) ∧ ((s1 - s + (s2 - s1) = s2 - s ∧ 0%Z ≤ s2 - s) ∧ k + 1%Z - 1%Z = k ∧ o8 ⊆ a ∖ b ∖ c ∧ partial_solution (k + 1%Z - 1%Z) col2 ∧ sorted sol2 s s2 ∧ (∀(i : Z) (j : Z), i ∈ o2 ∖ o8 -> j ∈ o8 -> i < j)) ∧ (∀(i : Z), s ≤ i ∧ i < s2 -> partial_solution n (sol2 i) ∧ eq_prefix col2 (sol2 i) (k + 1%Z - 1%Z) ∧ sol2 i (k + 1%Z - 1%Z) ∈ o2 ∖ o8) ∧ (∀(t : Z -> Z), partial_solution n t ∧ eq_prefix col2 t (k + 1%Z - 1%Z) ∧ t (k + 1%Z - 1%Z) ∈ o2 ∖ o8 -> t (k + 1%Z - 1%Z) ∈ o2 ∧ ¬ t (k + 1%Z - 1%Z) ∈ o8 ∧ (∃(i : Z), (s ≤ i ∧ i < s2) ∧ eq_prefix t (sol2 i) n)) ∧ eq_prefix col col2 (k + 1%Z - 1%Z) ∧ eq_prefix sol sol2 s))))))) else 0%Z ≤ s1 - s ∧ sorted sol1 s s1 ∧ (∀(t : Z -> Z), (partial_solution n t ∧ eq_prefix col1 t k) = (∃(i : Z), (s ≤ i ∧ i < s1) ∧ eq_prefix t (sol1 i) n)) ∧ eq_prefix col col1 k ∧ eq_prefix sol sol1 s))) else (1%Z = s + 1%Z - s ∧ 0%Z ≤ s + 1%Z - s) ∧ sorted (fun_updt sol s col) s (s + 1%Z) ∧ (∀(t : Z -> Z), (partial_solution n t ∧ eq_prefix col t k) = (∃(i : Z), (s ≤ i ∧ i < s + 1%Z) ∧ eq_prefix t (fun_updt sol s col i) n)) ∧ eq_prefix col col k ∧ eq_prefix sol (fun_updt sol s col) s.
Admitted.
