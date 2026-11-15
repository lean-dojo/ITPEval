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
Require Import koda_ruskey_vcg.koda_ruskey.KodaRuskey_Spec.
Require Import koda_ruskey_vcg.koda_ruskey.Lemmas.
Open Scope Z_scope.
Theorem main'vc (f0 : forest) (bits : list color) (fact0 : white_forest f0 (nth_i bits)) (fact1 : size_forest f0 = Z.of_nat (length bits)) (fact2 : valid_nums_forest f0 (Z.of_nat (length bits))) : let o1 : list forest := cons f0 ([] : list forest) in (size_forest f0 = Z.of_nat (length bits) ∧ valid_nums_forest f0 (Z.of_nat (length bits)) ∧ sub o1 f0 (nth_i bits) ∧ any_stack o1 (nth_i bits) ∧ valid_coloring f0 (nth_i bits)) ∧ (∀(bits1 : list color) (visited : list (Z -> color)), length bits1 = length bits -> (∀(i : Z), ¬ mem_stack i o1 -> nth (Z.to_nat i) bits1 inhabitant = nth (Z.to_nat i) bits inhabitant) ∧ inverse o1 (nth_i bits) (nth_i bits1) ∧ valid_coloring f0 (nth_i bits1) ∧ stored_solutions f0 (nth_i bits1) o1 ([] : list (Z -> color)) visited -> Z.of_nat (length visited) = count_forest f0 ∧ (let n : Z := Z.of_nat (length visited) in ∀(j : Z), 0%Z ≤ j ∧ j < n -> valid_coloring f0 (nth (Z.to_nat j) visited inhabitant) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < n -> ¬ j = k -> ¬ eq_coloring (Z.of_nat (length bits1)) (nth (Z.to_nat j) visited inhabitant) (nth (Z.to_nat k) visited inhabitant)))).
Admitted.
