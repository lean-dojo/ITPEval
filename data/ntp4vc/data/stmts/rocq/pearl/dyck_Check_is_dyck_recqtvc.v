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
Require Import dyck_vcg.dyck.Dyck.
Open Scope Z_scope.
Definition fall (p : list paren) (s : list paren) := dyck p ∧ (match s with | cons L _ => False | _ => True end).
Theorem is_dyck_rec'vc (w : list paren) : match w with | cons L w0 => (0%Z ≤ Z.of_nat (length w) ∧ Z.of_nat (length w0) < Z.of_nat (length w)) ∧ (∀(p0 : list paren), (∀(o1 : list paren), w0 = p0 ++ o1 ∧ fall p0 o1 ∧ (∀(p2 : list paren) (s : list paren), w0 = p2 ++ s ∧ fall p2 s -> p2 = p0 ∧ s = o1) -> (match o1 with | cons _ w1 => (0%Z ≤ Z.of_nat (length w) ∧ Z.of_nat (length w1) < Z.of_nat (length w)) ∧ (∀(p1 : list paren), (∀(w2 : list paren), w1 = p1 ++ w2 ∧ fall p1 w2 ∧ (∀(p2 : list paren) (s : list paren), w1 = p2 ++ s ∧ fall p2 s -> p2 = p1 ∧ s = w2) -> w = cons L (p0 ++ cons Dyck.R p1) ++ w2 ∧ fall (cons L (p0 ++ cons Dyck.R p1)) w2 ∧ (∀(p2 : list paren) (s : list paren), w = p2 ++ s ∧ fall p2 s -> p2 = cons L (p0 ++ cons Dyck.R p1) ∧ s = w2)) ∧ ((∀(p : list paren) (s : list paren), w1 = p ++ s -> ¬ fall p s) -> (∀(p : list paren) (s : list paren), w = p ++ s -> ¬ fall p s))) | _ => (∀(p : list paren) (s : list paren), w = p ++ s -> ¬ fall p s) end)) ∧ ((∀(p : list paren) (s : list paren), w0 = p ++ s -> ¬ fall p s) -> (∀(p : list paren) (s : list paren), w = p ++ s -> ¬ fall p s))) | _ => w = ([] : list paren) ++ w ∧ fall ([] : list paren) w ∧ (∀(p2 : list paren) (s : list paren), w = p2 ++ s ∧ fall p2 s -> p2 = ([] : list paren) ∧ s = w) end.
Admitted.
