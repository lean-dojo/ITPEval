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
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.compare.Compare.
Require Import multiprecision.valuation.Valuation.
Require Import multiprecision.util.Util.
Require Import multiprecision.ptralias.Alias.
Require Import multiprecision.util.UtilOld.
Require Import multiprecision.add.Add.
Require Import multiprecision.add.AddOld.
Require Import multiprecision.sub.SubOld.
Require Import multiprecision.mul.Mul.
Require Import multiprecision.mul.Mul_basecase.
Require Import multiprecision.logical.LogicalUtil.
Require Import multiprecision.logical.Logical.
Require Import multiprecision.logical.LogicalOld.
Require Import multiprecision.div.Div.
Require Import multiprecision.toom.Toom.
Require Import multiprecision.add_1.Add_1.
Require Import multiprecision.sub_1.Sub_1.
Open Scope Z_scope.
Definition redc (ur : Z) (u : Z) (n : Z) (m : Z) := ZEuclid.modulo ur m = ZEuclid.modulo (Z.pow (18446744073709551615%Z + 1%Z) n * u) m.
Theorem binvert_limb'vc (n : bv 64%N) (fact0 : Z.Odd (bv_unsigned n)) : (∀(n1 : Z) (inv : Z) (prec : Z), (0%Z ≤ n1 ∧ 0%Z ≤ inv) ∧ ZEuclid.modulo (inv * n1) (Z.pow 2%Z prec) = 1%Z ∧ 0%Z ≤ 2%Z * prec ∧ 2%Z * prec ≤ 64%Z -> ZEuclid.modulo (ZEuclid.modulo (2%Z * inv - inv * (inv * n1)) (18446744073709551615%Z + 1%Z) * n1) (Z.pow 2%Z (2%Z * prec)) = 1%Z) ∧ ¬ 2%Z = 0%Z ∧ uint'64_in_bounds (Z.rem (bv_unsigned n) 2%Z) ∧ (∀(o1 : bv 64%N), bv_unsigned o1 = Z.rem (bv_unsigned n) 2%Z -> (¬ 128%Z = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned o1) 128%Z)) ∧ (∀(h : bv 64%N), bv_unsigned h = Z.quot (bv_unsigned o1) 128%Z -> (0%Z ≤ bv_unsigned h ∧ bv_unsigned h < 128%Z) ∧ (∀(o2 : bv 64%N), (0%Z ≤ bv_unsigned o2 ∧ bv_unsigned o2 < 256%Z) ∧ ZEuclid.modulo (bv_unsigned o2 * (2%Z * bv_unsigned h + 1%Z)) (Z.pow 2%Z 8%Z) = 1%Z -> (∀(o3 : bv 64%N), bv_unsigned o3 = ZEuclid.modulo (bv_unsigned o2 * bv_unsigned n) (18446744073709551615%Z + 1%Z) -> (∀(o4 : bv 64%N), bv_unsigned o4 = ZEuclid.modulo (bv_unsigned o2 * bv_unsigned o3) (18446744073709551615%Z + 1%Z) -> (∀(o5 : bv 64%N), bv_unsigned o5 = ZEuclid.modulo (2%Z * bv_unsigned o2) (18446744073709551615%Z + 1%Z) -> (∀(o6 : bv 64%N), bv_unsigned o6 = ZEuclid.modulo (bv_unsigned o5 - bv_unsigned o4) (18446744073709551615%Z + 1%Z) -> (∀(o7 : bv 64%N), bv_unsigned o7 = ZEuclid.modulo (bv_unsigned o6 * bv_unsigned n) (18446744073709551615%Z + 1%Z) -> (∀(o8 : bv 64%N), bv_unsigned o8 = ZEuclid.modulo (bv_unsigned o6 * bv_unsigned o7) (18446744073709551615%Z + 1%Z) -> (∀(o9 : bv 64%N), bv_unsigned o9 = ZEuclid.modulo (2%Z * bv_unsigned o6) (18446744073709551615%Z + 1%Z) -> (∀(o10 : bv 64%N), bv_unsigned o10 = ZEuclid.modulo (bv_unsigned o9 - bv_unsigned o8) (18446744073709551615%Z + 1%Z) -> (∀(o11 : bv 64%N), bv_unsigned o11 = ZEuclid.modulo (bv_unsigned o10 * bv_unsigned n) (18446744073709551615%Z + 1%Z) -> (∀(o12 : bv 64%N), bv_unsigned o12 = ZEuclid.modulo (bv_unsigned o10 * bv_unsigned o11) (18446744073709551615%Z + 1%Z) -> (∀(o13 : bv 64%N), bv_unsigned o13 = ZEuclid.modulo (2%Z * bv_unsigned o10) (18446744073709551615%Z + 1%Z) -> (∀(o14 : bv 64%N), bv_unsigned o14 = ZEuclid.modulo (bv_unsigned o13 - bv_unsigned o12) (18446744073709551615%Z + 1%Z) -> ZEuclid.modulo (bv_unsigned o14 * bv_unsigned n) (18446744073709551615%Z + 1%Z) = 1%Z))))))))))))))).
Admitted.
