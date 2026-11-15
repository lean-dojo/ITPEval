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
Definition pal {α : Type} `{Inhabited α} (x : list α) (n : Z) := ∀(i : Z), 0%Z ≤ i ∧ i < n -> nth_error_i x i = nth_error_i x (n - 1%Z - i).
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom eq : elt -> elt -> Prop.
Axiom eq'spec : forall  (x : elt) (y : elt), eq x y = (x = y).
Theorem palindrome_rec'vc (y : list elt) (x : list elt) (fact0 : Z.of_nat (length y) ≤ Z.of_nat (length x)) : match y with | [] => (∃(x0 : list elt), length x0 = length y ∧ x = x0 ++ x) ∧ pal x (Z.of_nat (length y)) | cons x1 x2 => (match x2 with | [] => (match x with | cons x3 x4 => (∃(x0 : list elt), length x0 = length y ∧ x = x0 ++ x4) ∧ pal x (Z.of_nat (length y)) | _ => False end) | cons x3 x4 => (match x with | cons x5 x6 => ((match x with | [] => False | cons _ f => f = x6 end) ∧ Z.of_nat (length x4) ≤ Z.of_nat (length x6)) ∧ (∀(o1 : list elt), (∃(x0 : list elt), length x0 = length x4 ∧ x6 = x0 ++ o1) ∧ pal x6 (Z.of_nat (length x4)) -> (match o1 with | cons x11 xs => eq x5 x11 = (x5 = x11) -> (if decide (eq x5 x11) then (∃(x0 : list elt), length x0 = length y ∧ x = x0 ++ xs) ∧ pal x (Z.of_nat (length y)) else ∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length y)) ∧ ¬ nth_error_i x i = nth_error_i x (Z.of_nat (length y) - 1%Z - i)) | [] => False end)) ∧ ((∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length x4)) ∧ ¬ nth_error_i x6 i = nth_error_i x6 (Z.of_nat (length x4) - 1%Z - i)) -> (∃(i : Z), (0%Z ≤ i ∧ i < Z.of_nat (length y)) ∧ ¬ nth_error_i x i = nth_error_i x (Z.of_nat (length y) - 1%Z - i))) | _ => False end) end) end.
Admitted.
