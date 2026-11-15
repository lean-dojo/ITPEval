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
Theorem find'vc (l : list Z) (x : Z) (fact0 : Sorted Z.le l) : (match l with | [] => True | cons y r => ¬ x = y -> y < x -> (match l with | [] => False | cons _ f => f = r end) ∧ Sorted Z.le r end) ∧ (∀(result : bool), (match l with | [] => result = false | cons y r => (if decide (x = y) then result = true else if decide (y < x) then result = (if decide (x ∈ r) then true else false) else result = false) end) -> (result = true) = (x ∈ l)).
Admitted.
