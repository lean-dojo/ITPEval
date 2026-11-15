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
Theorem sub_n_ry'vc (sz : bv 32%N) (x : ptr (bv 64%N)) (y : ptr (bv 64%N)) (fact0 : 0%Z ≤ bv_signed sz) (fact1 : valid x (bv_signed sz)) (fact2 : valid y (bv_signed sz)) (fact3 : writable y = true) : valid y (bv_signed sz) ∧ valid x (bv_signed sz) ∧ 0%Z ≤ bv_signed sz ∧ bv_signed sz ≤ bv_signed sz ∧ writable y = true ∧ (∀(y1 : ptr (bv 64%N)) (x1 : ptr (bv 64%N)), offset y1 = offset y ∧ writable y1 = writable y ∧ zone1 y1 = zone1 y -> offset x1 = offset x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> (∀(nr : ptr (bv 64%N)) (ny : ptr (bv 64%N)) (nx : ptr (bv 64%N)) (m : mem), writable nr = true ∧ (value ny (bv_signed sz) = value y (bv_signed sz) ∧ value nx (bv_signed sz) = value x (bv_signed sz)) ∧ (valid ny (bv_signed sz) ∧ valid nx (bv_signed sz)) ∧ identical nr ny ∧ (0%Z ≤ offset ny ∧ offset ny + bv_signed sz ≤ offset nx ∨ 0%Z ≤ offset nx ∧ offset nx + bv_signed sz ≤ offset ny) ∧ (zx m = zone1 y1 ∧ zy m = zone1 x1) ∧ (bv_signed (mx m) = C.max y ∧ bv_signed (my m) = C.max x) ∧ (lx m = sz ∧ ly m = sz) ∧ ok m = true ∧ map_eq_sub_shift (pelts ny) (pelts y1) (offset ny) (offset y1) (bv_signed sz) ∧ map_eq_sub_shift (pelts nx) (pelts x1) (offset nx) (offset x1) (bv_signed sz) ∧ (pelts y1 = pelts y ∧ pelts x1 = pelts x) ∧ (plength y1 = plength y ∧ plength x1 = plength x) ∧ (min y1 = min y ∧ min x1 = min x) ∧ data nr = data ny ∧ data ny = data nx -> (0%Z ≤ bv_signed sz ∧ (valid nr (bv_signed sz) ∧ valid nx (bv_signed sz) ∧ valid ny (bv_signed sz)) ∧ (offset nr = offset nx ∨ offset nr + bv_signed sz ≤ offset nx ∨ offset nx + bv_signed sz ≤ offset nr) ∧ (offset nr = offset ny ∨ offset nr + bv_signed sz ≤ offset ny ∨ offset ny + bv_signed sz ≤ offset nr) ∧ (data nr = data nx ∧ data nx = data ny) ∧ writable nr = true) ∧ (∀(nx1 : ptr (bv 64%N)) (ny1 : ptr (bv 64%N)) (nr1 : ptr (bv 64%N)), data nx1 = data nr1 ∧ length (data nr1) = length (data nx) ∧ offset nx1 = offset nx ∧ min nx1 = min nx ∧ C.max nx1 = C.max nx ∧ writable nx1 = writable nx ∧ zone1 nx1 = zone1 nx -> data ny1 = data nr1 ∧ length (data nr1) = length (data ny) ∧ offset ny1 = offset ny ∧ min ny1 = min ny ∧ C.max ny1 = C.max ny ∧ writable ny1 = writable ny ∧ zone1 ny1 = zone1 ny -> length (data nr1) = length (data nr) ∧ offset nr1 = offset nr ∧ min nr1 = min nr ∧ C.max nr1 = C.max nr ∧ writable nr1 = writable nr ∧ zone1 nr1 = zone1 nr -> (∀(res : bv 64%N), value nr1 (bv_signed sz) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned res = value nx (bv_signed sz) - value ny (bv_signed sz) ∧ (0%Z ≤ bv_unsigned res ∧ bv_unsigned res ≤ 1%Z) ∧ (∀(j : Z), j < offset nr1 ∨ offset nr1 + bv_signed sz ≤ j -> pelts nr1 j = pelts nr j) ∧ (offset nr1 = offset nx1 ∨ map_eq_sub (pelts nx1) (pelts nx) (offset nx1) (offset nx1 + bv_signed sz)) ∧ (offset nr1 = offset ny1 ∨ map_eq_sub (pelts ny1) (pelts ny) (offset ny1) (offset ny1 + bv_signed sz)) -> ((writable y1 = true ∧ writable nr1 = true) ∧ ok m = true ∧ (0%Z ≤ bv_signed sz ∧ bv_signed sz ≤ bv_signed sz) ∧ identical nr1 ny1 ∧ (0%Z ≤ offset ny1 ∧ offset ny1 + bv_signed sz ≤ offset nx1 ∨ 0%Z ≤ offset nx1 ∧ offset nx1 + bv_signed sz ≤ offset ny1) ∧ (zx m = zone1 y1 ∧ zy m = zone1 x1) ∧ lx m = sz ∧ ly m = sz) ∧ (∀(m1 : mem) (nx2 : ptr (bv 64%N)) (ny2 : ptr (bv 64%N)) (y2 : ptr (bv 64%N)) (x2 : ptr (bv 64%N)), zr m1 = zr m ∧ zx m1 = zx m ∧ zy m1 = zy m ∧ mr m1 = mr m ∧ mx m1 = mx m ∧ my m1 = my m ∧ lr m1 = lr m ∧ lx m1 = lx m ∧ ly m1 = ly m -> offset nx2 = offset nx1 ∧ writable nx2 = writable nx1 ∧ zone1 nx2 = zone1 nx1 -> offset ny2 = offset ny1 ∧ writable ny2 = writable ny1 ∧ zone1 ny2 = zone1 ny1 -> offset y2 = offset y1 ∧ min y2 = min y1 ∧ writable y2 = writable y1 ∧ zone1 y2 = zone1 y1 -> offset x2 = offset x1 ∧ min x2 = min x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> (C.max y2 = bv_signed (mx m1) ∧ C.max x2 = bv_signed (my m1)) ∧ map_eq_sub_shift (pelts ny1) (pelts y2) (offset ny2) (offset y2) (bv_signed sz) ∧ map_eq_sub_shift (pelts nx1) (pelts x2) (offset nx2) (offset x2) (bv_signed sz) ∧ (∀(j : Z), j < offset y2 ∨ offset y2 + bv_signed sz ≤ j -> pelts y2 j = pelts y1 j) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sz ≤ j -> pelts x2 j = pelts x1 j) ∧ (plength y2 = plength y1 ∧ plength x2 = plength x1) ∧ min y2 = min y1 ∧ min x2 = min x1 -> value y2 (bv_signed sz) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sz) * bv_unsigned res = value x (bv_signed sz) - value y (bv_signed sz) ∧ (0%Z ≤ bv_unsigned res ∧ bv_unsigned res ≤ 1%Z) ∧ (∀(j : Z), j < offset y2 ∨ offset y2 + bv_signed sz ≤ j -> pelts y2 j = pelts y j) ∧ (∀(j : Z), pelts x2 j = pelts x j) ∧ value x2 (bv_signed sz) = value x (bv_signed sz) ∧ (min x2 = min x ∧ C.max x2 = C.max x ∧ plength x2 = plength x) ∧ min y2 = min y ∧ C.max y2 = C.max y ∧ plength y2 = plength y))))).
Admitted.
