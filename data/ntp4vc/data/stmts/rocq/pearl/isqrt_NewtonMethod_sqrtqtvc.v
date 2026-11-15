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
Theorem sqrt'vc (x : Z) (fact0 : 0%Z ≤ x) : if decide (x = 0%Z) then isqrt_spec x 0%Z else if decide (x ≤ 3%Z) then isqrt_spec x 1%Z else ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem (1%Z + x) 2%Z in (0%Z < o1 ∧ 0%Z < x ∧ o1 = Z.rem (Z.rem x x + x) 2%Z ∧ x < sqr (x + 1%Z) ∧ x < sqr (o1 + 1%Z)) ∧ (∀(y : Z), 0%Z < Z.rem (Z.rem x y + y) 2%Z ∧ 0%Z < y ∧ x < sqr (y + 1%Z) ∧ x < sqr (Z.rem (Z.rem x y + y) 2%Z + 1%Z) -> (if decide (Z.rem (Z.rem x y + y) 2%Z < y) then ¬ Z.rem (Z.rem x y + y) 2%Z = 0%Z ∧ ¬ 2%Z = 0%Z ∧ (0%Z ≤ y ∧ Z.rem (Z.rem x y + y) 2%Z < y) ∧ 0%Z < Z.rem (Z.rem x (Z.rem (Z.rem x y + y) 2%Z) + Z.rem (Z.rem x y + y) 2%Z) 2%Z ∧ 0%Z < Z.rem (Z.rem x y + y) 2%Z ∧ x < sqr (Z.rem (Z.rem x y + y) 2%Z + 1%Z) ∧ x < sqr (Z.rem (Z.rem x (Z.rem (Z.rem x y + y) 2%Z) + Z.rem (Z.rem x y + y) 2%Z) 2%Z + 1%Z) else isqrt_spec x y))).
Admitted.
