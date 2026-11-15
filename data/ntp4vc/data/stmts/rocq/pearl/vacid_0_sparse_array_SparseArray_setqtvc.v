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
Require Import Why3.map.MapInjection.
Open Scope Z_scope.
Axiom sparse_array : Type -> Type.
Axiom sparse_array_inhabited : forall  {α : Type} `{Inhabited α}, Inhabited (sparse_array α).
Global Existing Instance sparse_array_inhabited.
Axiom values : forall {α : Type} `{Inhabited α}, sparse_array α -> list α.
Axiom index : forall {α : Type} `{Inhabited α}, sparse_array α -> list Z.
Axiom back : forall {α : Type} `{Inhabited α}, sparse_array α -> list Z.
Axiom card : forall {α : Type} `{Inhabited α}, sparse_array α -> Z.
Axiom def1 : forall {α : Type} `{Inhabited α}, sparse_array α -> α.
Axiom sparse_array'invariant : forall  {α : Type} `{Inhabited α} (self : sparse_array α), 0%Z ≤ card self ∧ card self ≤ Z.of_nat (length (values self)) ∧ Z.of_nat (length (values self)) ≤ 1000%Z ∧ length (values self) = length (index self) ∧ length (index self) = length (back self) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < card self -> (0%Z ≤ nth (Z.to_nat i) (back self) inhabitant ∧ nth (Z.to_nat i) (back self) inhabitant < Z.of_nat (length (values self))) ∧ nth (Z.to_nat (nth (Z.to_nat i) (back self) inhabitant)) (index self) inhabitant = i).
Definition sparse_array'eq {α : Type} `{Inhabited α} (a : sparse_array α) (b : sparse_array α) := values a = values b ∧ index a = index b ∧ back a = back b ∧ card a = card b ∧ def1 a = def1 b.
Axiom sparse_array'inj : forall  {α : Type} `{Inhabited α} (a : sparse_array α) (b : sparse_array α) (fact0 : sparse_array'eq a b), a = b.
Definition is_elt {α : Type} `{Inhabited α} (a : sparse_array α) (i : Z) := (0%Z ≤ nth (Z.to_nat i) (index a) inhabitant ∧ nth (Z.to_nat i) (index a) inhabitant < card a) ∧ nth (Z.to_nat (nth (Z.to_nat i) (index a) inhabitant)) (back a) inhabitant = i.
Definition value {α : Type} `{Inhabited α} (a : sparse_array α) (i : Z) : α := if decide (is_elt a i) then nth (Z.to_nat i) (values a) inhabitant else def1 a.
Definition length {α : Type} `{Inhabited α} (a : sparse_array α) : Z := Z.of_nat (List.length (values a)).
Theorem set'vc {α : Type} `{Inhabited α} (i : Z) (a : sparse_array α) (v : α) (fact0 : 0%Z ≤ i) (fact1 : i < length a) : let o1 : list α := values a in (0%Z ≤ i ∧ i < Z.of_nat (List.length o1)) ∧ (∀(a1 : sparse_array α), List.length (set_list o1 (Z.to_nat i) v) = List.length o1 -> List.length (set_list o1 (Z.to_nat i) v) = List.length (values a) -> nth_i (set_list o1 (Z.to_nat i) v) = fun_updt (nth_i o1) i v -> ((0%Z ≤ card a ∧ card a ≤ Z.of_nat (List.length (set_list o1 (Z.to_nat i) v)) ∧ Z.of_nat (List.length (set_list o1 (Z.to_nat i) v)) ≤ 1000%Z) ∧ (List.length (set_list o1 (Z.to_nat i) v) = List.length (index a) ∧ List.length (index a) = List.length (back a)) ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < card a -> (0%Z ≤ nth (Z.to_nat i1) (back a) inhabitant ∧ nth (Z.to_nat i1) (back a) inhabitant < Z.of_nat (List.length (set_list o1 (Z.to_nat i) v))) ∧ nth (Z.to_nat (nth (Z.to_nat i1) (back a) inhabitant)) (index a) inhabitant = i1)) ∧ (def1 a = def1 a1 ∧ card a = card a1 ∧ back a = back a1 ∧ index a = index a1 ∧ set_list o1 (Z.to_nat i) v = values a1 -> (0%Z ≤ i ∧ i < length a1) ∧ (if decide (¬ is_elt a1 i) then let o2 : Z := card a1 in let o3 : list Z := index a1 in (0%Z ≤ i ∧ i < Z.of_nat (List.length o3)) ∧ (List.length (set_list o3 (Z.to_nat i) o2) = List.length o3 -> List.length (set_list o3 (Z.to_nat i) o2) = List.length (index a1) -> nth_i (set_list o3 (Z.to_nat i) o2) = fun_updt (nth_i o3) i o2 -> (0%Z ≤ card a1 ∧ card a1 < Z.of_nat (List.length (back a1))) ∧ (List.length (set_list (back a1) (Z.to_nat (card a1)) i) = List.length (back a1) -> List.length (set_list (back a1) (Z.to_nat (card a1)) i) = List.length (back a1) -> nth_i (set_list (back a1) (Z.to_nat (card a1)) i) = fun_updt (nth_i (back a1)) (card a1) i -> (∀(a2 : sparse_array α), ((0%Z ≤ card a1 + 1%Z ∧ card a1 + 1%Z ≤ Z.of_nat (List.length (values a1)) ∧ Z.of_nat (List.length (values a1)) ≤ 1000%Z) ∧ (List.length (values a1) = List.length (set_list o3 (Z.to_nat i) o2) ∧ List.length (set_list o3 (Z.to_nat i) o2) = List.length (set_list (back a1) (Z.to_nat (card a1)) i)) ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < card a1 + 1%Z -> (0%Z ≤ nth (Z.to_nat i1) (set_list (back a1) (Z.to_nat (card a1)) i) inhabitant ∧ nth (Z.to_nat i1) (set_list (back a1) (Z.to_nat (card a1)) i) inhabitant < Z.of_nat (List.length (values a1))) ∧ nth (Z.to_nat (nth (Z.to_nat i1) (set_list (back a1) (Z.to_nat (card a1)) i) inhabitant)) (set_list o3 (Z.to_nat i) o2) inhabitant = i1)) ∧ (def1 a1 = def1 a2 ∧ card a1 + 1%Z = card a2 ∧ set_list (back a1) (Z.to_nat (card a1)) i = back a2 ∧ set_list o3 (Z.to_nat i) o2 = index a2 ∧ values a1 = values a2 -> value a2 i = v ∧ (∀(j : Z), ¬ j = i -> value a2 j = value a j))))) else value a1 i = v ∧ (∀(j : Z), ¬ j = i -> value a1 j = value a j)))).
Admitted.
