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
Require Import Why3.int.Sum.
Require Import cursor_examples_vcg.cursor_examples.ListCursorImpl.
Open Scope Z_scope.
Axiom get_closure : forall {α : Type} `{Inhabited α}, list α -> Z -> α.
Axiom get_closure_def : forall  {α : Type} `{Inhabited α} (y : list α) (y1 : Z), get_closure y y1 = nth (Z.to_nat y1) y inhabitant.
Theorem list_sum'vc (c : cursor Z) (l : list Z) (fact0 : permitted c) (fact1 : visited c = ([] : list Z)) (fact2 : collection c = l) : 0%Z = sum (get_closure (visited c)) 0%Z (Z.of_nat (length (visited c))) ∧ permitted c ∧ (∀(c1 : cursor Z), collection c1 = collection c -> permitted c1 -> permitted c1 ∧ (if decide (¬ complete c1) then (¬ complete c1 ∧ permitted c1) ∧ (∀(c2 : cursor Z), collection c2 = collection c1 -> (∀(x : Z), visited c2 = visited c1 ++ [x] ∧ permitted c2 -> (0%Z ≤ Z.of_nat (length l) - Z.of_nat (length (visited c1)) ∧ Z.of_nat (length l) - Z.of_nat (length (visited c2)) < Z.of_nat (length l) - Z.of_nat (length (visited c1))) ∧ sum (get_closure (visited c1)) 0%Z (Z.of_nat (length (visited c1))) + x = sum (get_closure (visited c2)) 0%Z (Z.of_nat (length (visited c2))) ∧ permitted c2)) else sum (get_closure (visited c1)) 0%Z (Z.of_nat (length (visited c1))) = list_sum l)).
Admitted.
