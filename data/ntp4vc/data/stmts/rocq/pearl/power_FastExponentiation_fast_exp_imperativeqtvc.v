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
Open Scope Z_scope.
Theorem fast_exp_imperative'vc (n : Z) (x : Z) (fact0 : 0%Z ≤ n) : 0%Z ≤ n ∧ 1%Z * Z.pow x n = Z.pow x n ∧ (∀(e : Z) (p : Z) (r : Z), 0%Z ≤ e ∧ r * Z.pow p e = Z.pow x n -> (if decide (0%Z < e) then ¬ 2%Z = 0%Z ∧ (if decide (Z.quot e 2%Z = 1%Z) then ¬ 2%Z = 0%Z ∧ (0%Z ≤ e ∧ Z.rem e 2%Z < e) ∧ 0%Z ≤ Z.rem e 2%Z ∧ r * p * Z.pow (p * p) (Z.rem e 2%Z) = Z.pow x n else ¬ 2%Z = 0%Z ∧ (0%Z ≤ e ∧ Z.rem e 2%Z < e) ∧ 0%Z ≤ Z.rem e 2%Z ∧ r * Z.pow (p * p) (Z.rem e 2%Z) = Z.pow x n) else r = Z.pow x n)).
Admitted.
