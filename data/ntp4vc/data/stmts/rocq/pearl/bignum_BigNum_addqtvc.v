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
Theorem add'vc (n1 : list Z) (n2 : list Z) (fact0 : valid n1) (fact1 : valid n2) : valid n1 ∧ valid n2 ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ (∀(result : list Z), valid result ∧ value result = value n1 + value n2 + 0%Z -> valid result ∧ value result = value n1 + value n2).
Admitted.
