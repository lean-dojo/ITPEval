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
Axiom dll : Type.
Axiom dll_inhabited : Inhabited dll.
Global Existing Instance dll_inhabited.
Axiom dll_countable : Countable dll.
Global Existing Instance dll_countable.
Axiom prev : dll -> list Z.
Axiom next : dll -> list Z.
Axiom n : dll -> Z.
Axiom dll'invariant : forall  (self : dll), length (prev self) = length (next self) ∧ Z.of_nat (length (next self)) = n self.
Definition dll'eq (a : dll) (b : dll) := prev a = prev b ∧ next a = next b ∧ n a = n b.
Axiom dll'inj : forall  (a : dll) (b : dll) (fact0 : dll'eq a b), a = b.
Definition valid_in (l : dll) (i : Z) := (0%Z ≤ i ∧ i < n l) ∧ (0%Z ≤ nth (Z.to_nat i) (prev l) inhabitant ∧ nth (Z.to_nat i) (prev l) inhabitant < n l) ∧ (0%Z ≤ nth (Z.to_nat i) (next l) inhabitant ∧ nth (Z.to_nat i) (next l) inhabitant < n l) ∧ nth (Z.to_nat (nth (Z.to_nat i) (prev l) inhabitant)) (next l) inhabitant = i ∧ nth (Z.to_nat (nth (Z.to_nat i) (next l) inhabitant)) (prev l) inhabitant = i.
Definition valid_out (l : dll) (i : Z) := (0%Z ≤ i ∧ i < n l) ∧ (0%Z ≤ nth (Z.to_nat i) (prev l) inhabitant ∧ nth (Z.to_nat i) (prev l) inhabitant < n l) ∧ (0%Z ≤ nth (Z.to_nat i) (next l) inhabitant ∧ nth (Z.to_nat i) (next l) inhabitant < n l) ∧ nth (Z.to_nat (nth (Z.to_nat i) (prev l) inhabitant)) (next l) inhabitant = nth (Z.to_nat i) (next l) inhabitant ∧ nth (Z.to_nat (nth (Z.to_nat i) (next l) inhabitant)) (prev l) inhabitant = nth (Z.to_nat i) (prev l) inhabitant.
Definition is_list (l : dll) (s : list Z) := ∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length s) -> (0%Z ≤ nth (Z.to_nat k) s inhabitant ∧ nth (Z.to_nat k) s inhabitant < n l) ∧ nth (Z.to_nat (nth (Z.to_nat k) s inhabitant)) (prev l) inhabitant = nth (Z.to_nat (if decide (k = 0%Z) then Z.of_nat (length s) - 1%Z else k - 1%Z)) s inhabitant ∧ nth (Z.to_nat (nth (Z.to_nat k) s inhabitant)) (next l) inhabitant = nth (Z.to_nat (if decide (k = Z.of_nat (length s) - 1%Z) then 0%Z else k + 1%Z)) s inhabitant ∧ (∀(k' : Z), 0%Z ≤ k' ∧ k' < Z.of_nat (length s) -> ¬ k = k' -> ¬ nth (Z.to_nat k) s inhabitant = nth (Z.to_nat k') s inhabitant).
Theorem remove'vc (l : dll) (i : Z) (s : list Z) (fact0 : valid_in l i) (fact1 : is_list l (cons i s)) : let o1 : list Z := prev l in (0%Z ≤ i ∧ i < Z.of_nat (length o1)) ∧ (let o2 : Z := nth (Z.to_nat i) o1 inhabitant in let o3 : list Z := next l in (0%Z ≤ i ∧ i < Z.of_nat (length o3)) ∧ (let o4 : Z := nth (Z.to_nat i) o3 inhabitant in let o5 : list Z := prev l in (0%Z ≤ o4 ∧ o4 < Z.of_nat (length o5)) ∧ (length (set_list o5 (Z.to_nat o4) o2) = length o5 -> length (set_list o5 (Z.to_nat o4) o2) = length (prev l) -> nth_i (set_list o5 (Z.to_nat o4) o2) = fun_updt (nth_i o5) o4 o2 -> (0%Z ≤ i ∧ i < Z.of_nat (length (next l))) ∧ (let o6 : Z := nth (Z.to_nat i) (next l) inhabitant in (0%Z ≤ i ∧ i < Z.of_nat (length (set_list o5 (Z.to_nat o4) o2))) ∧ (let o7 : Z := nth (Z.to_nat i) (set_list o5 (Z.to_nat o4) o2) inhabitant in (0%Z ≤ o7 ∧ o7 < Z.of_nat (length (next l))) ∧ (∀(l1 : dll), length (set_list (next l) (Z.to_nat o7) o6) = length (next l) -> length (set_list (next l) (Z.to_nat o7) o6) = length (next l) -> nth_i (set_list (next l) (Z.to_nat o7) o6) = fun_updt (nth_i (next l)) o7 o6 -> (length (set_list o5 (Z.to_nat o4) o2) = length (set_list (next l) (Z.to_nat o7) o6) ∧ Z.of_nat (length (set_list (next l) (Z.to_nat o7) o6)) = n l) ∧ (n l = n l1 ∧ set_list (next l) (Z.to_nat o7) o6 = next l1 ∧ set_list o5 (Z.to_nat o4) o2 = prev l1 -> valid_out l1 i ∧ is_list l1 s))))))).
Admitted.
