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
Require Import Why3.mach.c.C.
Require Import Why3.mach.int.Unsigned.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.ptralias.Alias.
Open Scope Z_scope.
Theorem wmpn_add_n_in_place'vc (x : ptr (bv 64%N)) (sz : bv 32%N) (y : ptr (bv 64%N)) (fact0 : valid x (bv_signed sz)) (fact1 : valid y (bv_signed sz)) (fact2 : writable x = true) : 0%Z ≤ 0%Z ∧ 0%Z ≤ bv_signed sz ∧ value x 0%Z + Z.pow (18446744073709551615%Z + 1%Z) 0%Z * 0%Z = value x 0%Z + value y 0%Z ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ (∀(i : bv 32%N) (c : bv 64%N) (x1 : ptr (bv 64%N)), length (data x1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> (0%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ value x1 (bv_signed i) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed i) * bv_unsigned c = value x (bv_signed i) + value y (bv_signed i) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(j : Z), bv_signed i ≤ j ∧ j < bv_signed sz -> pelts x1 (offset x1 + j) = pelts x (offset x1 + j)) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sz ≤ j -> pelts x1 j = pelts x j) -> (if decide (bv_signed i < bv_signed sz) then (min x1 ≤ offset x1 + bv_signed i ∧ offset x1 + bv_signed i < C.max x1) ∧ (min y ≤ offset y + bv_signed i ∧ offset y + bv_signed i < C.max y) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(res : bv 64%N) (carry : bv 64%N), bv_unsigned res + (18446744073709551615%Z + 1%Z) * bv_unsigned carry = bv_unsigned (pelts x1 (offset x1 + bv_signed i)) + bv_unsigned (pelts y (offset y + bv_signed i)) + bv_unsigned c ∧ 0%Z ≤ bv_unsigned carry ∧ bv_unsigned carry ≤ 1%Z -> ((min x1 ≤ offset x1 + bv_signed i ∧ offset x1 + bv_signed i < C.max x1) ∧ writable x1 = true) ∧ (∀(x2 : ptr (bv 64%N)), length (data x2) = length (data x1) ∧ offset x2 = offset x1 ∧ min x2 = min x1 ∧ C.max x2 = C.max x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> pelts x2 = fun_updt (pelts x1) (offset x2 + bv_signed i) res ∧ pelts x2 (offset x2 + bv_signed i) = res -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed i + 1%Z -> (0%Z ≤ bv_signed sz - bv_signed i ∧ bv_signed sz - bv_signed o1 < bv_signed sz - bv_signed i) ∧ (0%Z ≤ bv_signed o1 ∧ bv_signed o1 ≤ bv_signed sz) ∧ value x2 (bv_signed o1) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed o1) * bv_unsigned carry = value x (bv_signed o1) + value y (bv_signed o1) ∧ (0%Z ≤ bv_unsigned carry ∧ bv_unsigned carry ≤ 1%Z) ∧ (∀(j : Z), bv_signed o1 ≤ j ∧ j < bv_signed sz -> pelts x2 (offset x2 + j) = pelts x (offset x2 + j)) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sz ≤ j -> pelts x2 j = pelts x j)))) else (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ value x1 (bv_signed sz) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned c = value x (bv_signed sz) + value y (bv_signed sz) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sz ≤ j -> pelts x1 j = pelts x j))).
Admitted.
