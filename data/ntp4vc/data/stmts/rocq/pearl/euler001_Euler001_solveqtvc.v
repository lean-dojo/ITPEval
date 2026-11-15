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
Require Import Why3.int.Div2.
Require Import euler001_vcg.euler001.DivModHints.
Require Import euler001_vcg.euler001.TriangularNumbers.
Require Import euler001_vcg.euler001.SumMultiple.
Open Scope Z_scope.
Theorem solve'vc (n : Z) (fact0 : 1%Z ≤ n) : ¬ 3%Z = 0%Z ∧ (let n3 : Z := Z.rem (n - 1%Z) 3%Z in ¬ 5%Z = 0%Z ∧ (let n5 : Z := Z.rem (n - 1%Z) 5%Z in ¬ 15%Z = 0%Z ∧ (let n15 : Z := Z.rem (n - 1%Z) 15%Z in ¬ 2%Z = 0%Z ∧ Z.rem (3%Z * n3 * (n3 + 1%Z) + 5%Z * n5 * (n5 + 1%Z) - 15%Z * n15 * (n15 + 1%Z)) 2%Z = sum_multiple_3_5_lt n))).
Admitted.
