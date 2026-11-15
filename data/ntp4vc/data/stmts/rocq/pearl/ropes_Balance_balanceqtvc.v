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
Theorem balance'vc (r : rope) (fact0 : inv r) (fact1 : Rope.length r < fib (max + 1%Z)) : let o1 : Z := max + 1%Z in 0%Z ≤ o1 ∧ (∀(q : list rope), (∀(i : Z), 0%Z ≤ i ∧ i < o1 -> nth (Z.to_nat i) q inhabitant = Emp) ∧ Z.of_nat (List.length q) = o1 -> ((2%Z < Z.of_nat (List.length q) ∧ Z.of_nat (List.length q) = max + 1%Z) ∧ inv r ∧ (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q inhabitant)) ∧ MyString.length (string_of_queue q) + Rope.length r < fib (max + 1%Z)) ∧ (∀(q1 : list rope), List.length q1 = List.length q -> (∀(j : Z), 2%Z ≤ j ∧ j ≤ max -> inv (nth (Z.to_nat j) q1 inhabitant)) ∧ infix_eqeq (string_of_queue q1) (MyString.app (string_of_queue q) (Rope.string r)) -> (let o2 : Z := max in (2%Z ≤ o2 + 1%Z -> (inv Emp ∧ infix_eqeq (Rope.string Emp) (string_of_array q1 2%Z 2%Z)) ∧ (∀(res : rope), (∀(i : Z), (2%Z ≤ i ∧ i ≤ o2) ∧ inv res ∧ infix_eqeq (Rope.string res) (string_of_array q1 2%Z i) -> (0%Z ≤ i ∧ i < Z.of_nat (List.length q1)) ∧ (let o3 : rope := nth (Z.to_nat i) q1 inhabitant in (inv o3 ∧ inv res) ∧ (∀(o4 : rope), inv o4 ∧ infix_eqeq (Rope.string o4) (MyString.app (Rope.string o3) (Rope.string res)) -> inv o4 ∧ infix_eqeq (Rope.string o4) (string_of_array q1 2%Z (i + 1%Z))))) ∧ (inv res ∧ infix_eqeq (Rope.string res) (string_of_array q1 2%Z (o2 + 1%Z)) -> inv res ∧ infix_eqeq (Rope.string res) (Rope.string r)))) ∧ (o2 + 1%Z < 2%Z -> (let result : rope := Emp in inv result ∧ infix_eqeq (Rope.string result) (Rope.string r)))))).
Admitted.
