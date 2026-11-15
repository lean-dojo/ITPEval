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
Require Import Why3.map.Const.
Require Import Why3.map.MapEq.
Require Import Why3.mach.int.Unsigned.
Require Import Why3.mach.c.C.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.lemmas.Lemmas.
Open Scope Z_scope.
Definition compare_int (x : Z) (y : Z) : Z := if decide (x < y) then - 1%Z else if decide (x = y) then 0%Z else 1%Z.
Theorem wmpn_cmp'vc (x : ptr (bv 64%N)) (sz : bv 32%N) (y : ptr (bv 64%N)) (fact0 : valid x (bv_signed sz)) (fact1 : valid y (bv_signed sz)) : 0%Z ≤ bv_signed sz ∧ bv_signed sz ≤ bv_signed sz ∧ (∀(j : Z), bv_signed sz ≤ j ∧ j < bv_signed sz -> pelts x (offset x + j) = pelts y (offset y + j)) ∧ (∀(i : bv 32%N), (0%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ (∀(j : Z), bv_signed i ≤ j ∧ j < bv_signed sz -> pelts x (offset x + j) = pelts y (offset y + j)) -> (if decide (1%Z ≤ bv_signed i) then int'32_in_bounds (bv_signed i - 1%Z) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed i - 1%Z -> (min x ≤ offset x + bv_signed o1 ∧ offset x + bv_signed o1 < C.max x) ∧ (let lx : bv 64%N := pelts x (offset x + bv_signed o1) in (min y ≤ offset y + bv_signed o1 ∧ offset y + bv_signed o1 < C.max y) ∧ (let ly : bv 64%N := pelts y (offset y + bv_signed o1) in ∀(o2 : bool), (bv_unsigned lx = bv_unsigned ly -> o2 = true) ∧ (o2 = true -> lx = ly) -> (if decide (¬ o2 = true) then if decide (bv_unsigned ly < bv_unsigned lx) then 1%Z = compare_int (value x (bv_signed sz)) (value y (bv_signed sz)) else - 1%Z = compare_int (value x (bv_signed sz)) (value y (bv_signed sz)) else bv_signed o1 < bv_signed i ∧ (0%Z ≤ bv_signed o1 ∧ bv_signed o1 ≤ bv_signed sz) ∧ (∀(j : Z), bv_signed o1 ≤ j ∧ j < bv_signed sz -> pelts x (offset x + j) = pelts y (offset y + j)))))) else 0%Z = compare_int (value x (bv_signed sz)) (value y (bv_signed sz)))).
Admitted.
