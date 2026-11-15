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
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom le : elt -> elt -> Prop.
Axiom Refl : forall  (x : elt), le x x.
Axiom Trans : forall  (x : elt) (y : elt) (z : elt) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom Total : forall  (x : elt) (y : elt), le x y ∨ le y x.
Inductive sorted : list elt -> Prop :=
 | Sorted_Nil : sorted ([] : list elt)
 | Sorted_One (x : elt) : sorted (cons x ([] : list elt))
 | Sorted_Two (x : elt) (y : elt) (l : list elt) : le x y -> sorted (cons y l) -> sorted (cons x (cons y l)).
Axiom sorted_mem : forall  (l : list elt) (x : elt), ((∀(y : elt), y ∈ l -> le x y) ∧ sorted l) = sorted (cons x l).
Axiom sorted_append : forall  (l1 : list elt) (l2 : list elt), (sorted l1 ∧ sorted l2 ∧ (∀(x : elt) (y : elt), x ∈ l1 -> y ∈ l2 -> le x y)) = sorted (l1 ++ l2).
Axiom prefix1 : forall {α : Type} `{Inhabited α}, Z -> list α -> list α.
Axiom prefix_def1 : forall  {α : Type} `{Inhabited α} (l : list α), prefix1 0%Z l = ([] : list α).
Axiom prefix_def2 : forall  {α : Type} `{Inhabited α} (n : Z) (x : α) (l : list α) (fact0 : 0%Z < n), prefix1 n (cons x l) = cons x (prefix1 (n - 1%Z) l).
Theorem chop'vc {α : Type} `{Inhabited α} (n : Z) (l : list α) (fact0 : 0%Z ≤ n) (fact1 : n ≤ Z.of_nat (length l)) : (¬ n = 0%Z -> (match l with | cons _ t => (let o1 : Z := n - 1%Z in (0%Z ≤ n ∧ o1 < n) ∧ 0%Z ≤ o1 ∧ o1 ≤ Z.of_nat (length t)) | [] => False end)) ∧ (∀(result : list α), (if decide (n = 0%Z) then result = l else match l with | cons _ t => t = prefix1 (n - 1%Z) t ++ result | [] => False end) -> l = prefix1 n l ++ result).
Admitted.
