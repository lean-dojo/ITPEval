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
Require Import isqrt_vcg.isqrt.Square.
Open Scope Z_scope.
Theorem isqrt'vc (x : Z) (fact0 : 0%Z ≤ x) : 0%Z ≤ 0%Z ∧ sqr 0%Z ≤ x ∧ 1%Z = sqr (0%Z + 1%Z) ∧ (∀(count : Z), 0%Z ≤ count ∧ sqr count ≤ x -> (if decide (sqr (count + 1%Z) ≤ x) then (0%Z ≤ x - count ∧ x - (count + 1%Z) < x - count) ∧ 0%Z ≤ count + 1%Z ∧ sqr (count + 1%Z) ≤ x ∧ sqr (count + 1%Z) + (2%Z * (count + 1%Z) + 1%Z) = sqr (count + 1%Z + 1%Z) else isqrt_spec x count)).
Admitted.
