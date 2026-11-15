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
Theorem wmpn_add_1_in_place'vc (x : ptr (bv 64%N)) (sz : bv 32%N) (y : bv 64%N) (fact0 : valid x (bv_signed sz)) (fact1 : 0%Z < bv_signed sz) (fact2 : writable x = true) : min x ≤ offset x ∧ offset x < C.max x ∧ (let o1 : bv 64%N := pelts x (offset x) in ∀(res : bv 64%N), bv_unsigned res = ZEuclid.modulo (bv_unsigned o1 + bv_unsigned y) (18446744073709551615%Z + 1%Z) -> ((min x ≤ offset x ∧ offset x < C.max x) ∧ writable x = true) ∧ (∀(x1 : ptr (bv 64%N)), length (data x1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> pelts x1 = fun_updt (pelts x) (offset x1) res -> (if decide (bv_unsigned res < bv_unsigned o1) then ((1%Z ≤ 1%Z ∧ 1%Z ≤ bv_signed sz) ∧ (0%Z ≤ bv_unsigned (1%bv : bv 64%N) ∧ bv_unsigned (1%bv : bv 64%N) ≤ 1%Z) ∧ (bv_unsigned (1%bv : bv 64%N) = 1%Z ∨ (1%bv : bv 32%N) = sz) ∧ value x1 1%Z + Z.pow (18446744073709551615%Z + 1%Z) 1%Z * bv_unsigned (1%bv : bv 64%N) = value x 1%Z + bv_unsigned y ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + 1%Z ≤ j -> pelts x1 j = pelts x j)) ∧ (∀(i : bv 32%N) (c : bv 64%N) (x2 : ptr (bv 64%N)), length (data x2) = length (data x1) ∧ offset x2 = offset x1 ∧ min x2 = min x1 ∧ C.max x2 = C.max x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> (1%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (bv_unsigned c = 1%Z ∨ i = sz) ∧ value x2 (bv_signed i) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed i) * bv_unsigned c = value x (bv_signed i) + bv_unsigned y ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed i ≤ j -> pelts x2 j = pelts x j) -> (if decide (bv_signed i < bv_signed sz) then (min x2 ≤ offset x2 + bv_signed i ∧ offset x2 + bv_signed i < C.max x2) ∧ (∀(res1 : bv 64%N), bv_unsigned res1 = ZEuclid.modulo (bv_unsigned (pelts x2 (offset x2 + bv_signed i)) + 1%Z) (18446744073709551615%Z + 1%Z) -> ((min x2 ≤ offset x2 + bv_signed i ∧ offset x2 + bv_signed i < C.max x2) ∧ writable x2 = true) ∧ (∀(x3 : ptr (bv 64%N)), length (data x3) = length (data x2) ∧ offset x3 = offset x2 ∧ min x3 = min x2 ∧ C.max x3 = C.max x2 ∧ writable x3 = writable x2 ∧ zone1 x3 = zone1 x2 -> pelts x3 = fun_updt (pelts x2) (offset x3 + bv_signed i) res1 ∧ pelts x3 (offset x3 + bv_signed i) = res1 -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o2 : bv 32%N), bv_signed o2 = bv_signed i + 1%Z -> (∀(o3 : bool), (bv_unsigned res1 = bv_unsigned (0%bv : bv 64%N) -> o3 = true) ∧ (o3 = true -> res1 = (0%bv : bv 64%N)) -> (if decide (¬ o3 = true) then value x3 (bv_signed sz) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned (0%bv : bv 64%N) = value x (bv_signed sz) + bv_unsigned y ∧ (0%Z ≤ bv_unsigned (0%bv : bv 64%N) ∧ bv_unsigned (0%bv : bv 64%N) ≤ 1%Z) ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed sz ≤ j -> pelts x3 j = pelts x j) else (0%Z ≤ bv_signed sz - bv_signed i ∧ bv_signed sz - bv_signed o2 < bv_signed sz - bv_signed i) ∧ (1%Z ≤ bv_signed o2 ∧ bv_signed o2 ≤ bv_signed sz) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (bv_unsigned c = 1%Z ∨ o2 = sz) ∧ value x3 (bv_signed o2) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed o2) * bv_unsigned c = value x (bv_signed o2) + bv_unsigned y ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed o2 ≤ j -> pelts x3 j = pelts x j)))))) else value x2 (bv_signed sz) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned c = value x (bv_signed sz) + bv_unsigned y ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sz ≤ j -> pelts x2 j = pelts x j))) else value x1 (bv_signed sz) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * 0%Z = value x (bv_signed sz) + bv_unsigned y ∧ (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sz ≤ j -> pelts x1 j = pelts x j)))).
Admitted.
