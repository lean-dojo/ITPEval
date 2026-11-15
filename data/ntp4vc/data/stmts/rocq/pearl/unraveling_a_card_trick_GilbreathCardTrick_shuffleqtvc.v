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
Require Import unraveling_a_card_trick_vcg.unraveling_a_card_trick.GilbreathCardTrickPure.
Require Import Why3.stack.Stack.
Open Scope Z_scope.
Theorem shuffle'vc (c : Stack.t Z) (a' : Stack.t Z) (b' : Stack.t Z) (a : Stack.t Z) (b : Stack.t Z) (fact0 : elts c = ([] : list Z)) (fact1 : elts a' = ([] : list Z)) (fact2 : elts b' = ([] : list Z)) : rev (elts a) = rev (elts a) ++ elts a' ∧ rev (elts b) = rev (elts b) ++ elts b' ∧ shuffle (elts a') (elts b') (elts c) ∧ (∀(b'1 : Stack.t Z) (a'1 : Stack.t Z) (c1 : Stack.t Z) (b1 : Stack.t Z) (a1 : Stack.t Z), rev (elts a) = rev (elts a1) ++ elts a'1 ∧ rev (elts b) = rev (elts b1) ++ elts b'1 ∧ shuffle (elts a'1) (elts b'1) (elts c1) -> (∀(o1 : bool), (if decide (elts a1 = ([] : list Z)) then o1 = (if decide (elts b1 = ([] : list Z)) then true else false) else o1 = false) -> (if decide (¬ o1 = true) then ∀(o2 : bool), (if decide (¬ elts a1 = ([] : list Z)) then elts b1 = ([] : list Z) -> o2 = true else o2 = false) -> (if decide (o2 = true) then ¬ elts a1 = ([] : list Z) ∧ (∀(o3 : Z), (match elts a1 with | [] => False | cons x _ => o3 = x end) -> (∀(a'2 : Stack.t Z), elts a'2 = cons o3 (elts a'1) -> ¬ elts a1 = ([] : list Z) ∧ (∀(a2 : Stack.t Z) (o4 : Z), (match elts a1 with | [] => False | cons x t => o4 = x ∧ elts a2 = t end) -> (∀(c2 : Stack.t Z), elts c2 = cons o4 (elts c1) -> (0%Z ≤ Stack.length a1 + Stack.length b1 ∧ Stack.length a2 + Stack.length b1 < Stack.length a1 + Stack.length b1) ∧ rev (elts a) = rev (elts a2) ++ elts a'2 ∧ rev (elts b) = rev (elts b1) ++ elts b'1 ∧ shuffle (elts a'2) (elts b'1) (elts c2))))) else ¬ elts b1 = ([] : list Z) ∧ (∀(o3 : Z), (match elts b1 with | [] => False | cons x _ => o3 = x end) -> (∀(b'2 : Stack.t Z), elts b'2 = cons o3 (elts b'1) -> ¬ elts b1 = ([] : list Z) ∧ (∀(b2 : Stack.t Z) (o4 : Z), (match elts b1 with | [] => False | cons x t => o4 = x ∧ elts b2 = t end) -> (∀(c2 : Stack.t Z), elts c2 = cons o4 (elts c1) -> (0%Z ≤ Stack.length a1 + Stack.length b1 ∧ Stack.length a1 + Stack.length b2 < Stack.length a1 + Stack.length b1) ∧ rev (elts a) = rev (elts a1) ++ elts a'1 ∧ rev (elts b) = rev (elts b2) ++ elts b'2 ∧ shuffle (elts a'1) (elts b'2) (elts c2)))))) else elts a1 = ([] : list Z) ∧ elts b1 = ([] : list Z) ∧ shuffle (rev (elts a)) (rev (elts b)) (elts c1)))).
Admitted.
