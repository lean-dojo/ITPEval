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
Theorem insert_leaves'vc (q : list rope) (r : rope) (fact0 : 2%Z < Z.of_nat (List.length q)) (fact1 : Z.of_nat (List.length q) = max + 1%Z) (fact2 : inv r) (fact3 : ∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) (fact4 : MyString.length (string_of_queue q) + Rope.length r < fib (max + 1%Z)) : match r with | Emp => (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) ∧ infix_eqeq (string_of_queue q) (MyString.app (string_of_queue q) (Rope.string r)) | Str _ _ _ => ((2%Z ≤ 2%Z ∧ 2%Z < Z.of_nat (List.length q) ∧ Z.of_nat (List.length q) = max + 1%Z) ∧ inv r ∧ (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) ∧ MyString.length (string_of_array q 2%Z (max + 1%Z)) + Rope.length r < fib (max + 1%Z)) ∧ (∀(q1 : list rope), List.length q1 = List.length q -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ (∀(j : Z), 2%Z ≤ j ∧ j < 2%Z -> nth (Z.to_nat j) q1 inhabitant = nth (Z.to_nat j) q inhabitant) ∧ infix_eqeq (string_of_array q1 2%Z (max + 1%Z)) (MyString.app (string_of_array q 2%Z (max + 1%Z)) (Rope.string r)) -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ infix_eqeq (string_of_queue q1) (MyString.app (string_of_queue q) (Rope.string r))) | App left1 right1 _ => ((match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = left1 ∨ f1 = left1 end) ∧ (2%Z < Z.of_nat (List.length q) ∧ Z.of_nat (List.length q) = max + 1%Z) ∧ inv left1 ∧ (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) ∧ MyString.length (string_of_queue q) + Rope.length left1 < fib (max + 1%Z)) ∧ (∀(q1 : list rope), List.length q1 = List.length q -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ infix_eqeq (string_of_queue q1) (MyString.app (string_of_queue q) (Rope.string left1)) -> ((match r with | Emp => False | Str _ _ _ => False | App f f1 _ => f = right1 ∨ f1 = right1 end) ∧ (2%Z < Z.of_nat (List.length q1) ∧ Z.of_nat (List.length q1) = max + 1%Z) ∧ inv right1 ∧ (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ MyString.length (string_of_queue q1) + Rope.length right1 < fib (max + 1%Z)) ∧ (∀(q2 : list rope), List.length q2 = List.length q1 -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q2 inhabitant)) ∧ infix_eqeq (string_of_queue q2) (MyString.app (string_of_queue q1) (Rope.string right1)) -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q2 inhabitant)) ∧ infix_eqeq (string_of_queue q2) (MyString.app (string_of_queue q) (Rope.string r)))) end.
Admitted.
