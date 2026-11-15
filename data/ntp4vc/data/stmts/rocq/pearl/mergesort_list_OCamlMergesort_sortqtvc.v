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
Theorem sort'vc (n : Z) (l : list elt) (fact0 : 2%Z ≤ n) (fact1 : n ≤ Z.of_nat (length l)) : (if decide (n = 2%Z) then match l with | cons x1 (cons x2 _) => True | _ => False end else if decide (n = 3%Z) then match l with | cons x1 (cons x2 (cons x3 _)) => True | _ => False end else ¬ 2%Z = 0%Z ∧ (let n1 : Z := Z.rem n 2%Z in let n2 : Z := n - n1 in (0%Z ≤ n1 ∧ n1 ≤ Z.of_nat (length l)) ∧ (∀(l2 : list elt), l = prefix1 n1 l ++ l2 -> ((0%Z ≤ n ∧ n1 < n) ∧ 2%Z ≤ n1 ∧ n1 ≤ Z.of_nat (length l)) ∧ (∀(s1 : list elt), sorted (rev s1) ∧ s1 ≡ₚ prefix1 n1 l -> ((0%Z ≤ n ∧ n2 < n) ∧ 2%Z ≤ n2 ∧ n2 ≤ Z.of_nat (length l2)) ∧ (∀(s2 : list elt), sorted (rev s2) ∧ s2 ≡ₚ prefix1 n2 l2 -> (let o1 : list elt := ([] : list elt) in (sorted o1 ∧ sorted (rev s1) ∧ sorted (rev s2)) ∧ (∀(x : elt) (y : elt), x ∈ o1 -> y ∈ s1 -> le y x) ∧ (∀(x : elt) (y : elt), x ∈ o1 -> y ∈ s2 -> le y x))))))) ∧ (∀(result : list elt), (if decide (n = 2%Z) then match l with | cons x1 (cons x2 _) => (if decide (le x1 x2) then result = cons x1 (cons x2 ([] : list elt)) else result = cons x2 (cons x1 ([] : list elt))) | _ => False end else if decide (n = 3%Z) then match l with | cons x1 (cons x2 (cons x3 _)) => (if decide (le x1 x2) then if decide (le x2 x3) then result = cons x1 (cons x2 (cons x3 ([] : list elt))) else if decide (le x1 x3) then result = cons x1 (cons x3 (cons x2 ([] : list elt))) else result = cons x3 (cons x1 (cons x2 ([] : list elt))) else if decide (le x1 x3) then result = cons x2 (cons x1 (cons x3 ([] : list elt))) else if decide (le x2 x3) then result = cons x2 (cons x3 (cons x1 ([] : list elt))) else result = cons x3 (cons x2 (cons x1 ([] : list elt)))) | _ => False end else let n1 : Z := Z.rem n 2%Z in ∃(l2 : list elt), l = prefix1 n1 l ++ l2 ∧ (∃(s1 : list elt), (sorted (rev s1) ∧ s1 ≡ₚ prefix1 n1 l) ∧ (∃(s2 : list elt), (sorted (rev s2) ∧ s2 ≡ₚ prefix1 (n - n1) l2) ∧ sorted result ∧ result ≡ₚ (([] : list elt) ++ s1) ++ s2))) -> sorted result ∧ result ≡ₚ prefix1 n l).
Admitted.
