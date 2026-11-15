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
Require Import Why3.real.Truncate.
Open Scope Z_scope.
Theorem sqrt'vc (r : R) (eps0 : R) (n : Z) (o1 : bool) (fact0 : Rle 0%R r) (fact1 : Rlt 0%R eps0) (fact2 : 1%Z ≤ n) (fact3 : if decide (Rlt r (Rmult (Rdefinitions.IZR n) eps0)) then o1 = (if decide (Rlt 1%R (Rmult (Rdefinitions.IZR n) eps0)) then true else false) else o1 = false) : (¬ o1 = true -> (let o2 : Z := 2%Z * n in (0%Z ≤ ceil (Rdiv (Rmax r 1%R) eps0) - n ∧ ceil (Rdiv (Rmax r 1%R) eps0) - o2 < ceil (Rdiv (Rmax r 1%R) eps0) - n) ∧ Rle 0%R r ∧ (Rlt 0%R eps0 ∧ 1%Z ≤ o2) ∧ Rmult 2%R (Rmult (Rdefinitions.IZR n) eps0) = Rmult (Rdefinitions.IZR o2) eps0)) ∧ (∀(result : R), (if decide (o1 = true) then result = 0%R else let o2 : R := Rmult 2%R (Rmult (Rdefinitions.IZR n) eps0) in ∃(r' : R), (Rle (Rmult r' r') r ∧ Rlt r (Rmult (Rplus r' o2) (Rplus r' o2))) ∧ (if decide (Rle (Rmult (Rplus r' (Rmult (Rdefinitions.IZR n) eps0)) (Rplus r' (Rmult (Rdefinitions.IZR n) eps0))) r) then result = Rplus r' (Rmult (Rdefinitions.IZR n) eps0) else result = r')) -> Rle (Rmult result result) r ∧ Rlt r (Rmult (Rplus result (Rmult (Rdefinitions.IZR n) eps0)) (Rplus result (Rmult (Rdefinitions.IZR n) eps0)))).
Admitted.
