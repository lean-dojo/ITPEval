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
Theorem card_trick'vc (a : Stack.t Z) (d' : Stack.t Z) (fact0 : Stack.length a = n * m) (fact1 : suit_ordered (elts a)) (fact2 : elts d' = ([] : list Z)) : (∃(result : Z), 0%Z ≤ result ∧ result ≤ n * m) ∧ (∀(cut : Z), 0%Z ≤ cut ∧ cut ≤ n * m -> (1%Z ≤ cut + 1%Z -> (Stack.length a = n * m - 1%Z + 1%Z ∧ Stack.length d' = 1%Z - 1%Z ∧ elts a = rev (elts d') ++ elts a) ∧ (∀(d_1 : Stack.t Z) (a1 : Stack.t Z), (∀(i : Z), (1%Z ≤ i ∧ i ≤ cut) ∧ Stack.length a1 = n * m - i + 1%Z ∧ Stack.length d_1 = i - 1%Z ∧ elts a = rev (elts d_1) ++ elts a1 -> ¬ elts a1 = ([] : list Z) ∧ (∀(a2 : Stack.t Z) (o1 : Z), (match elts a1 with | [] => False | cons x t => o1 = x ∧ elts a2 = t end) -> (∀(d_2 : Stack.t Z), elts d_2 = cons o1 (elts d_1) -> Stack.length a2 = n * m - (i + 1%Z) + 1%Z ∧ Stack.length d_2 = i + 1%Z - 1%Z ∧ elts a = rev (elts d_2) ++ elts a2))) ∧ (Stack.length a1 = n * m - (cut + 1%Z) + 1%Z ∧ Stack.length d_1 = cut + 1%Z - 1%Z ∧ elts a = rev (elts d_1) ++ elts a1 -> (∀(d_2 : Stack.t Z) (a2 : Stack.t Z) (result : Stack.t Z), elts a2 = ([] : list Z) ∧ elts d_2 = ([] : list Z) ∧ shuffle (rev (elts a1)) (rev (elts d_1)) (elts result) -> Stack.length result = n * m ∧ suit_sorted (elts result))))) ∧ (cut + 1%Z < 1%Z -> (∀(d_1 : Stack.t Z) (a1 : Stack.t Z) (result : Stack.t Z), elts a1 = ([] : list Z) ∧ elts d_1 = ([] : list Z) ∧ shuffle (rev (elts a)) (rev (elts d')) (elts result) -> Stack.length result = n * m ∧ suit_sorted (elts result)))).
Admitted.
