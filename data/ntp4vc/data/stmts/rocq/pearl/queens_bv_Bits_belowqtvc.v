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
Require Import Why3.why3.WellFounded.WellFounded.
Require Import queens_bv_vcg.queens_bv.S.
Open Scope Z_scope.
Axiom t : Type.
Axiom t_inhabited : Inhabited t.
Global Existing Instance t_inhabited.
Axiom t_countable : Countable t.
Global Existing Instance t_countable.
Axiom bv : t -> definitions.bv 32%N.
Axiom mdl : t -> gset Z.
Axiom t'invariant : forall  (i : Z) (self : t), ((0%Z ≤ i ∧ i < 32%Z) ∧ Z.testbit (bv_unsigned (bv self)) i = true) = (i ∈ mdl self).
Definition t'eq (a : t) (b : t) := bv a = bv b ∧ mdl a = mdl b.
Axiom t'inj : forall  (a : t) (b : t) (fact0 : t'eq a b), a = b.
Theorem below'vc (n : definitions.bv 32%N) (fact0 : bv_ule n (32%bv : definitions.bv 32%N)) : let o1 : gset Z := gset_interval 0%Z (bv_unsigned n) in let o2 : definitions.bv 32%N := bv_not (bv_shiftl (4294967295%bv : definitions.bv 32%N) n) in (∀(i : Z), ((0%Z ≤ i ∧ i < 32%Z) ∧ Z.testbit (bv_unsigned o2) i = true) = (i ∈ o1)) ∧ (∀(result : t), bv result = o2 ∧ mdl result = o1 -> mdl result = gset_interval 0%Z (bv_unsigned n)).
Admitted.
