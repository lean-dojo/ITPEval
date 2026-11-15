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
Theorem sub'vc (sy : bv 32%N) (sx : bv 32%N) (r : ptr (bv 64%N)) (x : ptr (bv 64%N)) (y : ptr (bv 64%N)) (fact0 : 0%Z ≤ bv_signed sy) (fact1 : bv_signed sy ≤ bv_signed sx) (fact2 : valid r (bv_signed sx)) (fact3 : valid x (bv_signed sx)) (fact4 : valid y (bv_signed sy)) (fact5 : writable r = true) : valid r (bv_signed sx) ∧ valid x (bv_signed sx) ∧ valid y (bv_signed sy) ∧ writable r = true ∧ 0%Z ≤ bv_signed sy ∧ bv_signed sy ≤ bv_signed sx ∧ (∀(y1 : ptr (bv 64%N)) (x1 : ptr (bv 64%N)) (r1 : ptr (bv 64%N)), offset y1 = offset y ∧ writable y1 = writable y ∧ zone1 y1 = zone1 y -> offset x1 = offset x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> offset r1 = offset r ∧ writable r1 = writable r ∧ zone1 r1 = zone1 r -> (∀(nr : ptr (bv 64%N)) (nx : ptr (bv 64%N)) (ny : ptr (bv 64%N)) (m : mem), writable nr = true ∧ (value nx (bv_signed sx) = value x (bv_signed sx) ∧ value ny (bv_signed sy) = value y (bv_signed sy)) ∧ (valid nr (bv_signed sx) ∧ valid nx (bv_signed sx) ∧ valid ny (bv_signed sy)) ∧ (0%Z ≤ offset nr ∧ offset nr + bv_signed sx ≤ offset nx ∧ offset nx + bv_signed sx ≤ offset ny) ∧ (zr m = zone1 r1 ∧ zx m = zone1 x1 ∧ zy m = zone1 y1) ∧ (bv_signed (mr m) = C.max r ∧ bv_signed (mx m) = C.max x ∧ bv_signed (my m) = C.max y) ∧ (lr m = sx ∧ lx m = sx ∧ ly m = sy) ∧ ok m = true ∧ map_eq_sub_shift (pelts nr) (pelts r1) (offset nr) (offset r1) (bv_signed sx) ∧ map_eq_sub_shift (pelts nx) (pelts x1) (offset nx) (offset x1) (bv_signed sx) ∧ map_eq_sub_shift (pelts ny) (pelts y1) (offset ny) (offset y1) (bv_signed sy) ∧ (pelts r1 = pelts r ∧ pelts x1 = pelts x ∧ pelts y1 = pelts y) ∧ (plength r1 = plength r ∧ plength x1 = plength x ∧ plength y1 = plength y) ∧ (min r1 = min r ∧ min x1 = min x ∧ min y1 = min y) ∧ data nr = data nx ∧ data nx = data ny -> ((0%Z ≤ bv_signed sy ∧ bv_signed sy ≤ bv_signed sx) ∧ (valid nr (bv_signed sx) ∧ valid nx (bv_signed sx) ∧ valid ny (bv_signed sy)) ∧ (offset nr = offset nx ∨ offset nr + bv_signed sx ≤ offset nx ∨ offset nx + bv_signed sx ≤ offset nr) ∧ (offset nr = offset ny ∨ offset nr + bv_signed sx ≤ offset ny ∨ offset ny + bv_signed sy ≤ offset nr) ∧ (data nr = data nx ∧ data nx = data ny) ∧ writable nr = true) ∧ (∀(ny1 : ptr (bv 64%N)) (nx1 : ptr (bv 64%N)) (nr1 : ptr (bv 64%N)), data ny1 = data nr1 ∧ length (data nr1) = length (data ny) ∧ offset ny1 = offset ny ∧ min ny1 = min ny ∧ C.max ny1 = C.max ny ∧ writable ny1 = writable ny ∧ zone1 ny1 = zone1 ny -> data nx1 = data nr1 ∧ length (data nr1) = length (data nx) ∧ offset nx1 = offset nx ∧ min nx1 = min nx ∧ C.max nx1 = C.max nx ∧ writable nx1 = writable nx ∧ zone1 nx1 = zone1 nx -> length (data nr1) = length (data nr) ∧ offset nr1 = offset nr ∧ min nr1 = min nr ∧ C.max nr1 = C.max nr ∧ writable nr1 = writable nr ∧ zone1 nr1 = zone1 nr -> (∀(res : bv 64%N), value nr1 (bv_signed sx) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned res = value nx (bv_signed sx) - value ny (bv_signed sy) ∧ (0%Z ≤ bv_unsigned res ∧ bv_unsigned res ≤ 1%Z) ∧ (∀(j : Z), j < offset nr1 ∨ offset nr1 + bv_signed sx ≤ j -> pelts nr1 j = pelts nr j) ∧ (offset nr1 = offset nx1 ∨ map_eq_sub (pelts nx1) (pelts nx) (offset nx1) (offset nx1 + bv_signed sx)) ∧ (offset nr1 = offset ny1 ∨ map_eq_sub (pelts ny1) (pelts ny) (offset ny1) (offset ny1 + bv_signed sy)) -> (ok m = true ∧ (0%Z ≤ bv_signed sy ∧ bv_signed sy ≤ bv_signed sx) ∧ (zr m = zone1 r1 ∧ zx m = zone1 x1 ∧ zy m = zone1 y1) ∧ (lr m = sx ∧ lx m = sx ∧ ly m = sy) ∧ (0%Z ≤ offset nr1 ∧ offset nr1 + bv_signed sx ≤ offset nx1 ∧ offset nx1 + bv_signed sx ≤ offset ny1) ∧ writable r1 = true ∧ writable nr1 = true) ∧ (∀(m1 : mem) (ny2 : ptr (bv 64%N)) (nx2 : ptr (bv 64%N)) (nr2 : ptr (bv 64%N)) (y2 : ptr (bv 64%N)) (x2 : ptr (bv 64%N)) (r2 : ptr (bv 64%N)), zr m1 = zr m ∧ zx m1 = zx m ∧ zy m1 = zy m ∧ mr m1 = mr m ∧ mx m1 = mx m ∧ my m1 = my m ∧ lr m1 = lr m ∧ lx m1 = lx m ∧ ly m1 = ly m -> offset ny2 = offset ny1 ∧ writable ny2 = writable ny1 ∧ zone1 ny2 = zone1 ny1 -> offset nx2 = offset nx1 ∧ writable nx2 = writable nx1 ∧ zone1 nx2 = zone1 nx1 -> offset nr2 = offset nr1 ∧ writable nr2 = writable nr1 ∧ zone1 nr2 = zone1 nr1 -> offset y2 = offset y1 ∧ min y2 = min y1 ∧ writable y2 = writable y1 ∧ zone1 y2 = zone1 y1 -> offset x2 = offset x1 ∧ min x2 = min x1 ∧ writable x2 = writable x1 ∧ zone1 x2 = zone1 x1 -> offset r2 = offset r1 ∧ min r2 = min r1 ∧ writable r2 = writable r1 ∧ zone1 r2 = zone1 r1 -> (C.max r2 = bv_signed (mr m1) ∧ C.max x2 = bv_signed (mx m1) ∧ C.max y2 = bv_signed (my m1)) ∧ map_eq_sub_shift (pelts nr1) (pelts r2) (offset nr2) (offset r2) (bv_signed sx) ∧ map_eq_sub_shift (pelts nx1) (pelts x2) (offset nx2) (offset x2) (bv_signed sx) ∧ map_eq_sub_shift (pelts ny1) (pelts y2) (offset ny2) (offset y2) (bv_signed sy) ∧ (∀(j : Z), j < offset r2 ∨ offset r2 + bv_signed sx ≤ j -> pelts r2 j = pelts r1 j) ∧ (∀(j : Z), j < offset x2 ∨ offset x2 + bv_signed sx ≤ j -> pelts x2 j = pelts x1 j) ∧ (∀(j : Z), j < offset y2 ∨ offset y2 + bv_signed sy ≤ j -> pelts y2 j = pelts y1 j) ∧ (plength r2 = plength r1 ∧ plength x2 = plength x1 ∧ plength y2 = plength y1) ∧ min r2 = min r1 ∧ min x2 = min x1 ∧ min y2 = min y1 -> value r2 (bv_signed sx) - Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned res = value x (bv_signed sx) - value y (bv_signed sy) ∧ (0%Z ≤ bv_unsigned res ∧ bv_unsigned res ≤ 1%Z) ∧ (∀(j : Z), j < offset r2 ∨ offset r2 + bv_signed sx ≤ j -> pelts r2 j = pelts r j) ∧ (∀(j : Z), pelts x2 j = pelts x j) ∧ (∀(j : Z), pelts y2 j = pelts y j) ∧ value x2 (bv_signed sx) = value x (bv_signed sx) ∧ value y2 (bv_signed sy) = value y (bv_signed sy) ∧ (min x2 = min x ∧ C.max x2 = C.max x ∧ plength x2 = plength x) ∧ (min y2 = min y ∧ C.max y2 = C.max y ∧ plength y2 = plength y) ∧ min r2 = min r ∧ C.max r2 = C.max r ∧ plength r2 = plength r))))).
Admitted.
