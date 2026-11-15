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
Theorem wmpn_sub_n'vc (sz : bv 32%N) (r : ptr (bv 64%N)) (x : ptr (bv 64%N)) (y : ptr (bv 64%N)) (fact0 : 0%Z ≤ bv_signed sz) (fact1 : valid r (bv_signed sz)) (fact2 : valid x (bv_signed sz)) (fact3 : valid y (bv_signed sz)) (fact4 : offset r = offset x ∨ offset r + bv_signed sz ≤ offset x ∨ offset x + bv_signed sz ≤ offset r) (fact5 : offset r = offset y ∨ offset r + bv_signed sz ≤ offset y ∨ offset y + bv_signed sz ≤ offset r) (fact6 : data r = data x) (fact7 : data x = data y) (fact8 : writable r = true) : 0%Z ≤ 0%Z ∧ 0%Z ≤ bv_signed sz ∧ value r 0%Z - Z.pow (18446744073709551615%Z + 1%Z) 0%Z * 0%Z = value x 0%Z - value y 0%Z ∧ pelts x = pelts r ∧ pelts r = pelts y ∧ (offset r = offset x ∨ map_eq_sub (pelts x) (pelts x) (offset x) (offset x + bv_signed sz)) ∧ (offset r = offset y ∨ map_eq_sub (pelts y) (pelts y) (offset y) (offset y + bv_signed sz)) ∧ 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ (∀(i : bv 32%N) (b : bv 64%N) (y1 : ptr (bv 64%N)) (x1 : ptr (bv 64%N)) (r1 : ptr (bv 64%N)), data y1 = data r1 ∧ length (data r1) = length (data y) ∧ offset y1 = offset y ∧ min y1 = min y ∧ C.max y1 = C.max y ∧ writable y1 = writable y ∧ zone1 y1 = zone1 y -> data x1 = data r1 ∧ length (data r1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> length (data r1) = length (data r) ∧ offset r1 = offset r ∧ min r1 = min r ∧ C.max r1 = C.max r ∧ writable r1 = writable r ∧ zone1 r1 = zone1 r -> (0%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ value r1 (bv_signed i) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed i) * bv_unsigned b = value x (bv_signed i) - value y (bv_signed i) ∧ (∀(j : Z), j < offset r1 ∨ offset r1 + bv_signed i ≤ j -> pelts r1 j = pelts r j) ∧ (pelts x1 = pelts r1 ∧ pelts r1 = pelts y1) ∧ (offset r1 = offset x1 ∨ map_eq_sub (pelts x1) (pelts x) (offset x1) (offset x1 + bv_signed sz)) ∧ (offset r1 = offset y1 ∨ map_eq_sub (pelts y1) (pelts y) (offset y1) (offset y1 + bv_signed sz)) ∧ 0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z -> (if decide (bv_signed i < bv_signed sz) then (min x1 ≤ offset x1 + bv_signed i ∧ offset x1 + bv_signed i < C.max x1) ∧ (min y1 ≤ offset y1 + bv_signed i ∧ offset y1 + bv_signed i < C.max y1) ∧ (min x ≤ offset x + bv_signed i ∧ offset x + bv_signed i < C.max x) ∧ (min y ≤ offset y + bv_signed i ∧ offset y + bv_signed i < C.max y) ∧ (0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z) ∧ (∀(res : bv 64%N) (borrow : bv 64%N), bv_unsigned res - (18446744073709551615%Z + 1%Z) * bv_unsigned borrow = bv_unsigned (pelts x1 (offset x1 + bv_signed i)) - bv_unsigned (pelts y1 (offset y1 + bv_signed i)) - bv_unsigned b ∧ 0%Z ≤ bv_unsigned borrow ∧ bv_unsigned borrow ≤ 1%Z -> ((min r1 ≤ offset r1 + bv_signed i ∧ offset r1 + bv_signed i < C.max r1) ∧ writable r1 = true) ∧ (∀(y2 : ptr (bv 64%N)) (x2 : ptr (bv 64%N)) (r2 : ptr (bv 64%N)), data y2 = data r2 ∧ length (data r2) = length (data y1) ∧ offset y2 = offset y1 ∧ min y2 = min y1 ∧ C.max y2 = C.max y1 ∧ writable y2 = writable y1 ∧ zone1 y2 = zone1 y1 -> data x2 = data r2 ∧ length (data r2) = length (data x1) ∧ offset x2 = offset x1 ∧ min x2 = min x1 ∧ C.max x2 = C.max x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> length (data r2) = length (data r1) ∧ offset r2 = offset r1 ∧ min r2 = min r1 ∧ C.max r2 = C.max r1 ∧ writable r2 = writable r1 ∧ zone1 r2 = zone1 r1 -> pelts r2 = fun_updt (pelts r1) (offset r2 + bv_signed i) res ∧ pelts r2 (offset r2 + bv_signed i) = res -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed i + 1%Z -> (0%Z ≤ bv_signed sz - bv_signed i ∧ bv_signed sz - bv_signed o1 < bv_signed sz - bv_signed i) ∧ (0%Z ≤ bv_signed o1 ∧ bv_signed o1 ≤ bv_signed sz) ∧ value r2 (bv_signed o1) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed o1) * bv_unsigned borrow = value x (bv_signed o1) - value y (bv_signed o1) ∧ (∀(j : Z), j < offset r2 ∨ offset r2 + bv_signed o1 ≤ j -> pelts r2 j = pelts r j) ∧ (pelts x2 = pelts r2 ∧ pelts r2 = pelts y2) ∧ (offset r2 = offset x2 ∨ map_eq_sub (pelts x2) (pelts x) (offset x2) (offset x2 + bv_signed sz)) ∧ (offset r2 = offset y2 ∨ map_eq_sub (pelts y2) (pelts y) (offset y2) (offset y2 + bv_signed sz)) ∧ 0%Z ≤ bv_unsigned borrow ∧ bv_unsigned borrow ≤ 1%Z))) else value r1 (bv_signed sz) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned b = value x (bv_signed sz) - value y (bv_signed sz) ∧ (0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z) ∧ (∀(j : Z), j < offset r1 ∨ offset r1 + bv_signed sz ≤ j -> pelts r1 j = pelts r j) ∧ (offset r1 = offset x1 ∨ map_eq_sub (pelts x1) (pelts x) (offset x1) (offset x1 + bv_signed sz)) ∧ (offset r1 = offset y1 ∨ map_eq_sub (pelts y1) (pelts y) (offset y1) (offset y1 + bv_signed sz)))).
Admitted.
