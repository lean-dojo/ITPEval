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
Axiom base : Z.
Axiom base'def : 1%Z < base.
Axiom digit : Type.
Axiom digit_inhabited : Inhabited digit.
Global Existing Instance digit_inhabited.
Axiom digit_countable : Countable digit.
Global Existing Instance digit_countable.
Axiom num : Type.
Axiom num_inhabited : Inhabited num.
Global Existing Instance num_inhabited.
Axiom num_countable : Countable num.
Global Existing Instance num_countable.
Axiom value : list Z -> Z.
Axiom value_def : forall (n : list Z), value n = (match n with | [] => 0%Z | cons d r => d + base * value r end).
Axiom valid : list Z -> Prop.
Axiom valid_def : forall (n : list Z), valid n = (match n with | [] => True | cons d [] => 0%Z < d ∧ d < base | cons d r => (0%Z ≤ d ∧ d < base) ∧ valid r end).
Theorem add_digit'vc (n : list Z) (d : Z) (fact0 : valid n) (fact1 : 0%Z ≤ d) (fact2 : d < base) : (match n with | [] => True | cons d0 r => ¬ d + d0 < base -> (match n with | [] => False | cons _ f => f = r end) ∧ valid r ∧ 0%Z ≤ 1%Z ∧ 1%Z < base end) ∧ (∀(result : list Z), (match n with | [] => (if decide (d = 0%Z) then result = ([] : list Z) else result = cons d ([] : list Z)) | cons d0 r => (if decide (d + d0 < base) then result = cons (d + d0) r else ∃(o1 : list Z), (valid o1 ∧ value o1 = value r + 1%Z) ∧ result = cons (d + d0 - base) o1) end) -> valid result ∧ value result = value n + d).
Admitted.
