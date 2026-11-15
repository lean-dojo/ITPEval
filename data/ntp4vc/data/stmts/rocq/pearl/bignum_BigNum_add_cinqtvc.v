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
Theorem add_cin'vc (n1 : list Z) (n2 : list Z) (cin : Z) (fact0 : valid n1) (fact1 : valid n2) (fact2 : 0%Z ≤ cin) (fact3 : cin ≤ 1%Z) : (match n2 with | [] => (match n1 with | [] => valid n2 ∧ 0%Z ≤ cin ∧ cin < base | cons x x1 => valid n1 ∧ 0%Z ≤ cin ∧ cin < base end) | cons x x1 => (match n1 with | [] => valid n2 ∧ 0%Z ≤ cin ∧ cin < base | cons x2 x3 => (if decide (cin + x2 + x < base) then (match n1 with | [] => False | cons _ f => f = x3 end) ∧ valid x3 ∧ valid x1 ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z else (match n1 with | [] => False | cons _ f => f = x3 end) ∧ valid x3 ∧ valid x1 ∧ 0%Z ≤ 1%Z ∧ 1%Z ≤ 1%Z) end) end) ∧ (∀(result : list Z), (match n2 with | [] => (match n1 with | [] => valid result ∧ value result = value n2 + cin | cons x x1 => valid result ∧ value result = value n1 + cin end) | cons x x1 => (match n1 with | [] => valid result ∧ value result = value n2 + cin | cons x2 x3 => (let d : Z := cin + x2 + x in if decide (d < base) then ∃(o1 : list Z), (valid o1 ∧ value o1 = value x3 + value x1 + 0%Z) ∧ result = cons d o1 else ∃(o1 : list Z), (valid o1 ∧ value o1 = value x3 + value x1 + 1%Z) ∧ result = cons (d - base) o1) end) end) -> valid result ∧ value result = value n1 + value n2 + cin).
Admitted.
