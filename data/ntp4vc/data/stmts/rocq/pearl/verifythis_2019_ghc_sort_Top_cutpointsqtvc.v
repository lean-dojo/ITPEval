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
Require Import Why3.exn.Exn.
Open Scope Z_scope.
Axiom Trans : forall  (x : Z) (y : Z) (z : Z) (fact0 : x < y) (fact1 : y < z), x < z.
Inductive sorted : list Z -> Prop :=
 | Sorted_Nil : sorted ([] : list Z)
 | Sorted_One (x : Z) : sorted (cons x ([] : list Z))
 | Sorted_Two (x : Z) (y : Z) (l : list Z) : x < y -> sorted (cons y l) -> sorted (cons x (cons y l)).
Axiom sorted_mem : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> x < y) ∧ sorted l) = sorted (cons x l).
Axiom sorted_append : forall  (l1 : list Z) (l2 : list Z), (sorted l1 ∧ sorted l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> x < y)) = sorted (l1 ++ l2).
Axiom Trans1 : forall  (x : Z) (y : Z) (z : Z) (fact0 : x ≤ y) (fact1 : y ≤ z), x ≤ z.
Inductive sorted1 : list Z -> Prop :=
 | Sorted_Nil1 : sorted1 ([] : list Z)
 | Sorted_One1 (x : Z) : sorted1 (cons x ([] : list Z))
 | Sorted_Two1 (x : Z) (y : Z) (l : list Z) : x ≤ y -> sorted1 (cons y l) -> sorted1 (cons x (cons y l)).
Axiom sorted_mem1 : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> x ≤ y) ∧ sorted1 l) = sorted1 (cons x l).
Axiom sorted_append1 : forall  (l1 : list Z) (l2 : list Z), (sorted1 l1 ∧ sorted1 l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> x ≤ y)) = sorted1 (l1 ++ l2).
Inductive sorted2 : list Z -> Prop :=
 | Sorted_Nil2 : sorted2 ([] : list Z)
 | Sorted_One2 (x : Z) : sorted2 (cons x ([] : list Z))
 | Sorted_Two2 (y : Z) (x : Z) (l : list Z) : y ≤ x -> sorted2 (cons y l) -> sorted2 (cons x (cons y l)).
Axiom sorted_mem2 : forall  (l : list Z) (x : Z), ((∀(y : Z), y ∈ l -> y ≤ x) ∧ sorted2 l) = sorted2 (cons x l).
Axiom sorted_append2 : forall  (l1 : list Z) (l2 : list Z), (sorted2 l1 ∧ sorted2 l2 ∧ (∀(x : Z) (y : Z), x ∈ l1 -> y ∈ l2 -> y ≤ x)) = sorted2 (l1 ++ l2).
Definition compat (s : list Z) (t : list Z) := match (s, t) with | (cons x _, cons y _) => x ≤ y | (_, _) => True end.
Axiom rev_append_sorted_incr : forall  (s : list Z) (t : list Z), sorted1 (rev_append s t) = (sorted2 s ∧ sorted1 t ∧ compat s t).
Axiom rev_append_sorted_decr : forall  (s : list Z) (t : list Z), sorted2 (rev_append s t) = (sorted1 s ∧ sorted2 t ∧ compat t s).
Definition eqb (b1 : bool) (b2 : bool) : bool := implb b1 b2 && implb b2 b1.
Axiom eqb'spec : forall  (b1 : bool) (b2 : bool), (eqb b1 b2 = true) = (b1 = b2).
Axiom list_seq : Type.
Axiom list_seq_inhabited : Inhabited list_seq.
Global Existing Instance list_seq_inhabited.
Axiom list_seq_countable : Countable list_seq.
Global Existing Instance list_seq_countable.
Axiom list : list_seq -> Datatypes.list Z.
Axiom seq : list_seq -> Datatypes.list Z.
Axiom list_seq'invariant : forall  (self : list_seq), seq self = rev (list self).
Definition list_seq'eq (a : list_seq) (b : list_seq) := list a = list b ∧ seq a = seq b.
Axiom list_seq'inj : forall  (a : list_seq) (b : list_seq) (fact0 : list_seq'eq a b), a = b.
Axiom nil : list_seq.
Axiom nil'def : list nil = ([] : Datatypes.list Z) ∧ seq nil = ([] : Datatypes.list Z).
Theorem cutpoints'vc (s : Datatypes.list Z) (fact0 : 0%Z < Z.of_nat (length s)) : let n : Z := Z.of_nat (length s) in ∀(o1 : list_seq), list o1 = cons 0%Z (list nil) -> (1%Z = 0%Z + 1%Z ∧ (0%Z < 1%Z ∧ 1%Z ≤ n + 1%Z) ∧ 0%Z < Z.of_nat (length (seq o1)) ∧ nth 0%nat (seq o1) inhabitant = 0%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq o1)) - 1%Z)) (seq o1) inhabitant = 0%Z ∧ (∀(z : Z), z ∈ list o1 -> 0%Z ≤ z ∧ z ≤ n) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq o1)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq o1) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq o1) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length (seq o1)) -> nth (Z.to_nat i) (seq o1) inhabitant ≤ nth (Z.to_nat j) (seq o1) inhabitant)) ∧ (∀(cut : list_seq), (0%Z < nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ≤ n + 1%Z) ∧ 0%Z < Z.of_nat (length (seq cut)) ∧ nth 0%nat (seq cut) inhabitant = 0%Z ∧ (∀(z : Z), z ∈ list cut -> 0%Z ≤ z ∧ z ≤ n) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq cut)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq cut) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq cut) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length (seq cut)) -> nth (Z.to_nat i) (seq cut) inhabitant ≤ nth (Z.to_nat j) (seq cut) inhabitant) -> (if decide (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z < n) then (0%Z ≤ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z < Z.of_nat (length s)) ∧ (0%Z ≤ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ∧ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant < Z.of_nat (length s)) ∧ ((nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ≤ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ≤ n) ∧ ((∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(y : Z), (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ≤ y ∧ y ≤ n) ∧ ((∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < y -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < y -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant)) -> (y < n -> (0%Z ≤ y ∧ y < Z.of_nat (length s)) ∧ (let o2 : Z := y - 1%Z in 0%Z ≤ o2 ∧ o2 < Z.of_nat (length s))) ∧ (∀(o2 : bool), (if decide (y < n) then let o3 : bool := (if decide (nth (Z.to_nat (y - 1%Z)) s inhabitant < nth (Z.to_nat y) s inhabitant) then true else false) in o2 = eqb o3 (if decide (nth (Z.to_nat (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant)) s inhabitant < nth (Z.to_nat (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z)) s inhabitant) then true else false) ∧ (o2 = true) = (o3 = (if decide (nth (Z.to_nat (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant)) s inhabitant < nth (Z.to_nat (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z)) s inhabitant) then true else false)) else o2 = false) -> (if decide (o2 = true) then (0%Z ≤ n - y ∧ n - (y + 1%Z) < n - y) ∧ (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z ≤ y + 1%Z ∧ y + 1%Z ≤ n) ∧ ((∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < y + 1%Z -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant ≤ z1 ∧ z1 < z2 ∧ z2 < y + 1%Z -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant)) else ∀(o3 : list_seq), list o3 = cons y (list cut) -> (0%Z ≤ n - (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z) ∧ n - (y + 1%Z) < n - (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant + 1%Z)) ∧ (0%Z < y + 1%Z ∧ y + 1%Z ≤ n + 1%Z) ∧ 0%Z < Z.of_nat (length (seq o3)) ∧ nth 0%nat (seq o3) inhabitant = 0%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq o3)) - 1%Z)) (seq o3) inhabitant = y ∧ (∀(z : Z), z ∈ list o3 -> 0%Z ≤ z ∧ z ≤ n) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq o3)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq o3) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq o3) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length (seq o3)) -> nth (Z.to_nat i) (seq o3) inhabitant ≤ nth (Z.to_nat j) (seq o3) inhabitant)))) else if decide (nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant < n) then ∀(o2 : list_seq), list o2 = cons n (list cut) -> nth 0%nat (seq o2) inhabitant = 0%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq o2)) - 1%Z)) (seq o2) inhabitant = Z.of_nat (length s) ∧ 2%Z ≤ Z.of_nat (length (list o2)) ∧ (∀(z : Z), z ∈ list o2 -> 0%Z ≤ z ∧ z ≤ Z.of_nat (length s)) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq o2)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq o2) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq o2) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length (seq o2)) -> nth (Z.to_nat i) (seq o2) inhabitant ≤ nth (Z.to_nat j) (seq o2) inhabitant) else nth 0%nat (seq cut) inhabitant = 0%Z ∧ nth (Z.to_nat (Z.of_nat (length (seq cut)) - 1%Z)) (seq cut) inhabitant = Z.of_nat (length s) ∧ 2%Z ≤ Z.of_nat (length (list cut)) ∧ (∀(z : Z), z ∈ list cut -> 0%Z ≤ z ∧ z ≤ Z.of_nat (length s)) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < Z.of_nat (length (seq cut)) - 1%Z -> (let ck : Z := nth (Z.to_nat k) (seq cut) inhabitant in let ck1 : Z := nth (Z.to_nat (k + 1%Z)) (seq cut) inhabitant in (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z1) s inhabitant < nth (Z.to_nat z2) s inhabitant) ∨ (∀(z1 : Z) (z2 : Z), ck ≤ z1 ∧ z1 < z2 ∧ z2 < ck1 -> nth (Z.to_nat z2) s inhabitant ≤ nth (Z.to_nat z1) s inhabitant))) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < Z.of_nat (length (seq cut)) -> nth (Z.to_nat i) (seq cut) inhabitant ≤ nth (Z.to_nat j) (seq cut) inhabitant))).
Admitted.
