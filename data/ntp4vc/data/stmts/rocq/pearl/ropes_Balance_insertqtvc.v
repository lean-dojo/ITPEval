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
Require Import Why3.int.Fibonacci.
Require Import ropes_vcg.ropes.MyString.
Require Import ropes_vcg.ropes.Rope.
Open Scope Z_scope.
Axiom max : Z.
Axiom max'def : 2%Z ≤ max.
Axiom string_of_array : list rope -> Z -> Z -> char_string.
Axiom string_of_array_empty : forall  (l : Z) (q : list rope) (fact0 : 0%Z ≤ l) (fact1 : l ≤ Z.of_nat (List.length q)), infix_eqeq (string_of_array q l l) MyString.empty.
Axiom string_of_array_concat_left : forall  (l : Z) (u : Z) (q : list rope) (fact0 : 0%Z ≤ l) (fact1 : l < u) (fact2 : u ≤ Z.of_nat (List.length q)), infix_eqeq (string_of_array q l u) (MyString.app (string_of_array q (l + 1%Z) u) (Rope.string (nth (Z.to_nat l) q inhabitant))).
Definition string_of_queue (q : list rope) : char_string := string_of_array q 2%Z (Z.of_nat (List.length q)).
Theorem insert'vc (i : Z) (q : list rope) (r : rope) (fact0 : 2%Z ≤ i) (fact1 : i < Z.of_nat (List.length q)) (fact2 : Z.of_nat (List.length q) = max + 1%Z) (fact3 : inv r) (fact4 : ∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) (fact5 : MyString.length (string_of_array q i (max + 1%Z)) + Rope.length r < fib (max + 1%Z)) : 0%Z ≤ i ∧ i < Z.of_nat (List.length q) ∧ (let o1 : rope := nth (Z.to_nat i) q inhabitant in (inv o1 ∧ inv r) ∧ (∀(r' : rope), inv r' ∧ infix_eqeq (Rope.string r') (MyString.app (Rope.string o1) (Rope.string r)) -> (let o2 : Z := i + 1%Z in 0%Z ≤ o2 ∧ (if decide (Rope.length r' < fib o2) then (0%Z ≤ i ∧ i < Z.of_nat (List.length q)) ∧ (List.length (set_list q (Z.to_nat i) r') = List.length q -> nth_i (set_list q (Z.to_nat i) r') = fun_updt (nth_i q) i r' -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) (set_list q (Z.to_nat i) r') inhabitant)) ∧ (∀(j : Z), 2%Z ≤ j ∧ j < i -> nth (Z.to_nat j) (set_list q (Z.to_nat i) r') inhabitant = nth (Z.to_nat j) q inhabitant) ∧ infix_eqeq (string_of_array (set_list q (Z.to_nat i) r') i (max + 1%Z)) (MyString.app (string_of_array q i (max + 1%Z)) (Rope.string r))) else let o3 : rope := Emp in (0%Z ≤ i ∧ i < Z.of_nat (List.length q)) ∧ (List.length (set_list q (Z.to_nat i) o3) = List.length q -> nth_i (set_list q (Z.to_nat i) o3) = fun_updt (nth_i q) i o3 -> (let o4 : Z := i + 1%Z in ((0%Z ≤ max - i ∧ max - o4 < max - i) ∧ (2%Z ≤ o4 ∧ o4 < Z.of_nat (List.length (set_list q (Z.to_nat i) o3)) ∧ Z.of_nat (List.length (set_list q (Z.to_nat i) o3)) = max + 1%Z) ∧ inv r' ∧ (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) (set_list q (Z.to_nat i) o3) inhabitant)) ∧ MyString.length (string_of_array (set_list q (Z.to_nat i) o3) o4 (max + 1%Z)) + Rope.length r' < fib (max + 1%Z)) ∧ (∀(q1 : list rope), List.length q1 = List.length (set_list q (Z.to_nat i) o3) -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ (∀(j : Z), 2%Z ≤ j ∧ j < o4 -> nth (Z.to_nat j) q1 inhabitant = nth (Z.to_nat j) (set_list q (Z.to_nat i) o3) inhabitant) ∧ infix_eqeq (string_of_array q1 o4 (max + 1%Z)) (MyString.app (string_of_array (set_list q (Z.to_nat i) o3) o4 (max + 1%Z)) (Rope.string r')) -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ (∀(j : Z), 2%Z ≤ j ∧ j < i -> nth (Z.to_nat j) q1 inhabitant = nth (Z.to_nat j) q inhabitant) ∧ infix_eqeq (string_of_array q1 i (max + 1%Z)) (MyString.app (string_of_array q i (max + 1%Z)) (Rope.string r))))))))).
Admitted.
