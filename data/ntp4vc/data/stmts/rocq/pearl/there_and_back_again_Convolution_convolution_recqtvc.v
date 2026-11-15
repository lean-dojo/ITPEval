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
Theorem convolution_rec'vc {α : Type} `{Inhabited α} (x : list α) (y : list α) (fact0 : Z.of_nat (length x) ≤ Z.of_nat (length y)) : (match x with | [] => True | cons x0 xs => ((match x with | [] => False | cons _ f => f = xs end) ∧ Z.of_nat (length xs) ≤ Z.of_nat (length y)) ∧ (∀(o1 : list (α * α)) (o2 : list α), (∃(y0 : list α), y = y0 ++ o2 ∧ length y0 = length xs ∧ o1 = zip xs (rev y0)) -> (match o2 with | cons x1 x2 => True | _ => False end)) end) ∧ (∀(r : list (α * α)) (ys : list α), (match x with | [] => r = ([] : list (α * α)) ∧ ys = y | cons x0 xs => (∃(r1 : list (α * α)) (ys1 : list α), (∃(y0 : list α), y = y0 ++ ys1 ∧ length y0 = length xs ∧ r1 = zip xs (rev y0)) ∧ (match ys1 with | cons x1 x2 => r = cons (x0, x1) r1 ∧ ys = x2 | _ => False end)) end) -> (∃(y0 : list α), y = y0 ++ ys ∧ length y0 = length x ∧ r = zip x (rev y0))).
Admitted.
