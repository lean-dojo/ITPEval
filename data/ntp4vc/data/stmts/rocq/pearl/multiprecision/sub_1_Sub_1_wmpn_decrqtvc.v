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
Theorem wmpn_decr'vc (x : ptr (bv 64%N)) (sz : bv 32%N) (y : bv 64%N) (fact0 : valid x (bv_signed sz)) (fact1 : 0%Z < bv_signed sz) (fact2 : 0%Z ≤ value x (bv_signed sz) - bv_unsigned y) (fact3 : writable x = true) : min x ≤ offset x ∧ offset x < C.max x ∧ (let o1 : bv 64%N := pelts x (offset x) in (min x ≤ offset x + 1%Z ∧ offset x + 1%Z ≤ C.max x) ∧ (∀(o2 : ptr (bv 64%N)), offset o2 = offset x + 1%Z ∧ plength o2 = plength x ∧ pelts o2 = pelts x ∧ data o2 = data x ∧ min o2 = min x ∧ C.max o2 = C.max x ∧ zone1 o2 = zone1 x ∧ writable o2 = writable x -> (∀(res : bv 64%N), bv_unsigned res = ZEuclid.modulo (bv_unsigned o1 - bv_unsigned y) (18446744073709551615%Z + 1%Z) -> ((min x ≤ offset x ∧ offset x < C.max x) ∧ writable x = true) ∧ (∀(xp : ptr (bv 64%N)) (x1 : ptr (bv 64%N)), data xp = data x1 ∧ length (data x1) = length (data o2) ∧ offset xp = offset o2 ∧ min xp = min o2 ∧ C.max xp = C.max o2 ∧ writable xp = writable o2 ∧ zone1 xp = zone1 o2 -> length (data x1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> pelts x1 = fun_updt (pelts x) (offset x1) res -> (if decide (bv_unsigned o1 < bv_unsigned res) then ((1%Z ≤ 1%Z ∧ 1%Z ≤ bv_signed sz) ∧ offset xp = offset x1 + 1%Z ∧ pelts xp = pelts x1 ∧ plength xp = plength x1 ∧ (min xp = min x1 ∧ C.max xp = C.max x1) ∧ ((1%bv : bv 32%N) = sz -> bv_unsigned (1%bv : bv 64%N) = 0%Z) ∧ (0%Z ≤ bv_unsigned (1%bv : bv 64%N) ∧ bv_unsigned (1%bv : bv 64%N) ≤ 1%Z) ∧ writable xp = true ∧ value x1 1%Z - Z.pow (18446744073709551615%Z + 1%Z) 1%Z * bv_unsigned (1%bv : bv 64%N) = value x 1%Z - bv_unsigned y ∧ (∀(j : Z), 1%Z ≤ j ∧ j < bv_signed sz -> pelts x1 (offset x1 + j) = pelts x (offset x1 + j)) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sz ≤ j -> pelts x1 j = pelts x j)) ∧ (∀(i : bv 32%N) (xp1 : ptr (bv 64%N)) (b : bv 64%N) (x2 : ptr (bv 64%N)), length (data x2) = length (data x1) ∧ offset x2 = offset x1 ∧ min x2 = min x1 ∧ C.max x2 = C.max x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> (1%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ offset xp1 = offset x2 + bv_signed i ∧ pelts xp1 = pelts x2 ∧ plength xp1 = plength x2 ∧ (min xp1 = min x2 ∧ C.max xp1 = C.max x2) ∧ (i = sz -> bv_unsigned b = 0%Z) ∧ (0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z) ∧ writable xp1 = true ∧ value x2 (bv_signed i) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed i) * bv_unsigned b = value x (bv_signed i) - bv_unsigned y ∧ (∀(j : Z), bv_signed i ≤ j ∧ j < bv_signed sz -> pelts x2 (offset x2 + j) = pelts x (offset x2 + j)) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sz ≤ j -> pelts x2 j = pelts x j) -> (∀(o3 : bool), (bv_unsigned b = bv_unsigned (0%bv : bv 64%N) -> o3 = true) ∧ (o3 = true -> b = (0%bv : bv 64%N)) -> (if decide (¬ o3 = true) then (min xp1 ≤ offset xp1 ∧ offset xp1 < C.max xp1) ∧ (∀(res1 : bv 64%N), bv_unsigned res1 = ZEuclid.modulo (bv_unsigned (pelts xp1 (offset xp1)) - 1%Z) (18446744073709551615%Z + 1%Z) -> ((min xp1 ≤ offset xp1 ∧ offset xp1 < C.max xp1) ∧ writable xp1 = true) ∧ (∀(xp2 : ptr (bv 64%N)) (x3 : ptr (bv 64%N)), data xp2 = data x3 ∧ length (data x3) = length (data xp1) ∧ offset xp2 = offset xp1 ∧ min xp2 = min xp1 ∧ C.max xp2 = C.max xp1 ∧ writable xp2 = writable xp1 ∧ zone1 xp2 = zone1 xp1 -> data xp2 = data x3 ∧ length (data x3) = length (data xp1) ∧ offset xp2 = offset xp1 ∧ min xp2 = min xp1 ∧ C.max xp2 = C.max xp1 ∧ writable xp2 = writable xp1 ∧ zone1 xp2 = zone1 xp1 -> length (data x3) = length (data x2) ∧ offset x3 = offset x2 ∧ min x3 = min x2 ∧ C.max x3 = C.max x2 ∧ writable x3 = writable x2 ∧ zone1 x3 = zone1 x2 -> pelts xp2 = fun_updt (pelts xp1) (offset xp2) res1 -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o4 : bv 32%N), bv_signed o4 = bv_signed i + 1%Z -> (min xp2 ≤ offset xp2 + 1%Z ∧ offset xp2 + 1%Z ≤ C.max xp2) ∧ (∀(o5 : ptr (bv 64%N)), offset o5 = offset xp2 + 1%Z ∧ plength o5 = plength xp2 ∧ pelts o5 = pelts xp2 ∧ data o5 = data xp2 ∧ min o5 = min xp2 ∧ C.max o5 = C.max xp2 ∧ zone1 o5 = zone1 xp2 ∧ writable o5 = writable xp2 -> (∀(o6 : bool), (bv_unsigned (pelts xp1 (offset xp1)) = bv_unsigned (0%bv : bv 64%N) -> o6 = true) ∧ (o6 = true -> pelts xp1 (offset xp1) = (0%bv : bv 64%N)) -> (if decide (¬ o6 = true) then value x3 (bv_signed sz) = value x (bv_signed sz) - bv_unsigned y ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed sz ≤ j -> pelts x3 j = pelts x j) else (0%Z ≤ bv_signed sz - bv_signed i ∧ bv_signed sz - bv_signed o4 < bv_signed sz - bv_signed i) ∧ (1%Z ≤ bv_signed o4 ∧ bv_signed o4 ≤ bv_signed sz) ∧ offset o5 = offset x3 + bv_signed o4 ∧ pelts o5 = pelts x3 ∧ plength o5 = plength x3 ∧ (min o5 = min x3 ∧ C.max o5 = C.max x3) ∧ (o4 = sz -> bv_unsigned b = 0%Z) ∧ (0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z) ∧ writable o5 = true ∧ value x3 (bv_signed o4) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed o4) * bv_unsigned b = value x (bv_signed o4) - bv_unsigned y ∧ (∀(j : Z), bv_signed o4 ≤ j ∧ j < bv_signed sz -> pelts x3 (offset x3 + j) = pelts x (offset x3 + j)) ∧ (∀(j : Z), j < offset x3 ∨ offset x3 + bv_signed sz ≤ j -> pelts x3 j = pelts x j))))))) else value x2 (bv_signed sz) = value x (bv_signed sz) - bv_unsigned y ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sz ≤ j -> pelts x2 j = pelts x j)))) else value x1 (bv_signed sz) = value x (bv_signed sz) - bv_unsigned y ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sz ≤ j -> pelts x1 j = pelts x j)))))).
Admitted.
