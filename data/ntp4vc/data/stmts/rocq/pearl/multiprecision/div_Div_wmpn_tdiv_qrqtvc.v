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
Require Import multiprecision.compare.Compare.
Require Import multiprecision.util.Util.
Require Import multiprecision.ptralias.Alias.
Require Import multiprecision.util.UtilOld.
Require Import multiprecision.add.Add.
Require Import multiprecision.add.AddOld.
Require Import multiprecision.sub.SubOld.
Require Import multiprecision.logical.LogicalUtil.
Require Import multiprecision.logical.LogicalOld.
Require Import multiprecision.mul.Mul.
Open Scope Z_scope.
Definition reciprocal (v : bv 64%N) (d : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned d) - (18446744073709551615%Z + 1%Z).
Definition reciprocal_3by2 (v : bv 64%N) (dh : bv 64%N) (dl : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh) - (18446744073709551615%Z + 1%Z).
Definition normalized (x : ptr (bv 64%N)) (sz : bv 32%N) := valid x (bv_signed sz) ∧ ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned (pelts x (offset x + bv_signed sz - 1%Z)).
Theorem wmpn_tdiv_qr'vc (sy : bv 32%N) (sx : bv 32%N) (x : ptr (bv 64%N)) (y : ptr (bv 64%N)) (q : ptr (bv 64%N)) (r : ptr (bv 64%N)) (qxn : bv 32%N) (fact0 : 1%Z ≤ bv_signed sy) (fact1 : bv_signed sy ≤ bv_signed sx) (fact2 : bv_signed sx ≤ 2147483647%Z - 1%Z) (fact3 : valid x (bv_signed sx)) (fact4 : valid y (bv_signed sy)) (fact5 : valid q (bv_signed sx - bv_signed sy + 1%Z)) (fact6 : valid r (bv_signed sy)) (fact7 : writable q = true) (fact8 : writable r = true) (fact9 : bv_signed qxn = 0%Z) (fact10 : 0%Z < bv_unsigned (pelts y (offset y + bv_signed sy - 1%Z))) : 0%Z ≤ bv_signed sx ∧ (∀(o1 : bv 32%N), bv_unsigned o1 = bv_signed sx -> uint'32_in_bounds (bv_unsigned o1 + 1%Z) ∧ (∀(o2 : bv 32%N), bv_unsigned o2 = bv_unsigned o1 + 1%Z -> 0%Z ≤ bv_unsigned o2 ∧ (∀(nx : ptr (bv 64%N)), (¬ zone1 nx = null_zone -> plength nx = bv_unsigned o2) ∧ offset nx = 0%Z ∧ min nx = 0%Z ∧ C.max nx = plength nx ∧ writable nx = true -> is_not_null nx = (¬ zone1 nx = null_zone) -> is_not_null nx -> 0%Z ≤ bv_signed sy ∧ (∀(o3 : bv 32%N), bv_unsigned o3 = bv_signed sy -> 0%Z ≤ bv_unsigned o3 ∧ (∀(ny : ptr (bv 64%N)), (¬ zone1 ny = null_zone -> plength ny = bv_unsigned o3) ∧ offset ny = 0%Z ∧ min ny = 0%Z ∧ C.max ny = plength ny ∧ writable ny = true -> is_not_null ny = (¬ zone1 ny = null_zone) -> is_not_null ny -> ((1%Z ≤ bv_signed sy ∧ bv_signed sy ≤ bv_signed sx ∧ bv_signed sx ≤ 2147483647%Z - 1%Z) ∧ valid x (bv_signed sx) ∧ valid y (bv_signed sy) ∧ valid q (bv_signed sx - bv_signed sy + 1%Z) ∧ valid r (bv_signed sy) ∧ valid nx (bv_signed sx + 1%Z) ∧ valid ny (bv_signed sy) ∧ (writable nx = true ∧ writable ny = true) ∧ 0%Z < bv_unsigned (pelts y (offset y + bv_signed sy - 1%Z)) ∧ writable q = true ∧ writable r = true) ∧ (∀(ny1 : ptr (bv 64%N)) (nx1 : ptr (bv 64%N)) (r1 : ptr (bv 64%N)) (q1 : ptr (bv 64%N)), length (data ny1) = length (data ny) ∧ offset ny1 = offset ny ∧ min ny1 = min ny ∧ C.max ny1 = C.max ny ∧ writable ny1 = writable ny ∧ zone1 ny1 = zone1 ny -> length (data nx1) = length (data nx) ∧ offset nx1 = offset nx ∧ min nx1 = min nx ∧ C.max nx1 = C.max nx ∧ writable nx1 = writable nx ∧ zone1 nx1 = zone1 nx -> length (data r1) = length (data r) ∧ offset r1 = offset r ∧ min r1 = min r ∧ C.max r1 = C.max r ∧ writable r1 = writable r ∧ zone1 r1 = zone1 r -> length (data q1) = length (data q) ∧ offset q1 = offset q ∧ min q1 = min q ∧ C.max q1 = C.max q ∧ writable q1 = writable q ∧ zone1 q1 = zone1 q -> value x (bv_signed sx) = value q1 (bv_signed sx - bv_signed sy + 1%Z) * value y (bv_signed sy) + value r1 (bv_signed sy) ∧ value r1 (bv_signed sy) < value y (bv_signed sy) -> (offset nx1 = 0%Z ∧ min nx1 = 0%Z ∧ C.max nx1 = plength nx1 ∧ writable nx1 = true) ∧ (offset ny1 = 0%Z ∧ min ny1 = 0%Z ∧ C.max ny1 = plength ny1 ∧ writable ny1 = true) ∧ value x (bv_signed sx) = value q1 (bv_signed sx - bv_signed sy + 1%Z) * value y (bv_signed sy) + value r1 (bv_signed sy) ∧ value r1 (bv_signed sy) < value y (bv_signed sy))))))).
Admitted.
