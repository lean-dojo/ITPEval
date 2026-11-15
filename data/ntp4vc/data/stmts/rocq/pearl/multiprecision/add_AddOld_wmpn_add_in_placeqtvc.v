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
Theorem wmpn_add_in_place'vc (sy : bv 32%N) (sx : bv 32%N) (x : ptr (bv 64%N)) (y : ptr (bv 64%N)) (fact0 : 0%Z ≤ bv_signed sy) (fact1 : bv_signed sy ≤ bv_signed sx) (fact2 : valid x (bv_signed sx)) (fact3 : valid y (bv_signed sy)) (fact4 : writable x = true) : valid x (bv_signed sy) ∧ valid y (bv_signed sy) ∧ writable x = true ∧ (∀(x1 : ptr (bv 64%N)), length (data x1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> (∀(o1 : bv 64%N), (0%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 ≤ 1%Z) ∧ value x1 (bv_signed sy) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sy) * bv_unsigned o1 = value x (bv_signed sy) + value y (bv_signed sy) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sy ≤ j -> pelts x1 j = pelts x j) -> (∀(o2 : bool), (bv_unsigned o1 = bv_unsigned (0%bv : bv 64%N) -> o2 = true) ∧ (o2 = true -> o1 = (0%bv : bv 64%N)) -> (if decide (¬ o2 = true) then ((bv_signed sy ≤ bv_signed sy ∧ bv_signed sy ≤ bv_signed sx) ∧ value x1 (bv_signed sy) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sy) * bv_unsigned o1 = value x (bv_signed sy) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 ≤ 1%Z) ∧ (sy = sx ∨ bv_unsigned o1 = 1%Z) ∧ (∀(j : Z), bv_signed sy ≤ j ∧ j < bv_signed sx -> pelts x1 (offset x1 + j) = pelts x (offset x1 + j)) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sx ≤ j -> pelts x1 j = pelts x j)) ∧ (∀(i : bv 32%N) (c : bv 64%N) (x2 : ptr (bv 64%N)), length (data x2) = length (data x1) ∧ offset x2 = offset x1 ∧ min x2 = min x1 ∧ C.max x2 = C.max x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> (bv_signed sy ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sx) ∧ value x2 (bv_signed i) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed i) * bv_unsigned c = value x (bv_signed i) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (i = sx ∨ bv_unsigned c = 1%Z) ∧ (∀(j : Z), bv_signed i ≤ j ∧ j < bv_signed sx -> pelts x2 (offset x2 + j) = pelts x (offset x2 + j)) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sx ≤ j -> pelts x2 j = pelts x j) -> (if decide (bv_signed i < bv_signed sx) then (min x2 ≤ offset x2 + bv_signed i ∧ offset x2 + bv_signed i < C.max x2) ∧ (∀(res : bv 64%N), bv_unsigned res = ZEuclid.modulo (bv_unsigned (pelts x2 (offset x2 + bv_signed i)) + 1%Z) (18446744073709551615%Z + 1%Z) -> ((min x2 ≤ offset x2 + bv_signed i ∧ offset x2 + bv_signed i < C.max x2) ∧ writable x2 = true) ∧ (∀(x3 : ptr (bv 64%N)), length (data x3) = length (data x2) ∧ offset x3 = offset x2 ∧ min x3 = min x2 ∧ C.max x3 = C.max x2 ∧ writable x3 = writable x2 ∧ zone1 x3 = zone1 x2 -> pelts x3 = fun_updt (pelts x2) (offset x3 + bv_signed i) res ∧ pelts x3 (offset x3 + bv_signed i) = res -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o3 : bv 32%N), bv_signed o3 = bv_signed i + 1%Z -> (∀(o4 : bool), (bv_unsigned res = bv_unsigned (0%bv : bv 64%N) -> o4 = true) ∧ (o4 = true -> res = (0%bv : bv 64%N)) -> (if decide (¬ o4 = true) then value x3 (bv_signed sx) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned (0%bv : bv 64%N) = value x (bv_signed sx) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned (0%bv : bv 64%N) ∧ bv_unsigned (0%bv : bv 64%N) ≤ 1%Z) ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed sx ≤ j -> pelts x3 j = pelts x j) else (0%Z ≤ bv_signed sx - bv_signed i ∧ bv_signed sx - bv_signed o3 < bv_signed sx - bv_signed i) ∧ (bv_signed sy ≤ bv_signed o3 ∧ bv_signed o3 ≤ bv_signed sx) ∧ value x3 (bv_signed o3) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed o3) * bv_unsigned c = value x (bv_signed o3) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (o3 = sx ∨ bv_unsigned c = 1%Z) ∧ (∀(j : Z), bv_signed o3 ≤ j ∧ j < bv_signed sx -> pelts x3 (offset x3 + j) = pelts x (offset x3 + j)) ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed sx ≤ j -> pelts x3 j = pelts x j)))))) else value x2 (bv_signed sx) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned c = value x (bv_signed sx) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sx ≤ j -> pelts x2 j = pelts x j))) else value x1 (bv_signed sx) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned o1 = value x (bv_signed sx) + value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 ≤ 1%Z) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sx ≤ j -> pelts x1 j = pelts x j))))).
Admitted.
