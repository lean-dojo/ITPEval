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
Require Import Why3.mach.c.UChar.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.powm.Powm.
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
Require Import multiprecision.stringlemmas.String_lemmas.
Require Import multiprecision.base_info.BaseInfo.
Open Scope Z_scope.
Theorem wmpn_limb_get_str'vc (binfo : wmpn_base_info) (sp : ptr (bv 8%N)) (d1 : bv 64%N) (shift : bv 64%N) (di : bv 64%N) (sz : bv 32%N) (w : bv 64%N) (fact0 : 2%Z ≤ b binfo) (fact1 : b binfo ≤ 256%Z) (fact2 : writable sp = true) (fact3 : ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned d1) (fact4 : 0%Z ≤ bv_unsigned shift) (fact5 : bv_unsigned shift ≤ 63%Z) (fact6 : b binfo * Z.pow 2%Z (bv_unsigned shift) = bv_unsigned d1) (fact7 : reciprocal di d1) (fact8 : valid sp (bv_signed sz)) (fact9 : 0%Z < bv_signed sz) (fact10 : bv_unsigned w < Z.pow (b binfo) (bv_signed sz)) : let base : Z := b binfo in ((0%Z ≤ bv_unsigned w ∧ bv_unsigned w < 18446744073709551615%Z + 1%Z) ∧ (0%Z ≤ 0%Z ∧ 0%Z ≤ bv_signed sz) ∧ (0%Z < bv_unsigned w -> 0%Z ≤ 0%Z ∧ 0%Z < bv_signed sz) ∧ in_base base (pelts sp) (offset sp) (offset sp + 0%Z) ∧ (bv_unsigned w = 0%Z -> 0%Z < 0%Z -> 0%Z < bv_signed (pelts sp (offset sp + 0%Z - 1%Z))) ∧ bv_unsigned w = svalue_le base sp 0%Z + Z.pow base 0%Z * bv_unsigned w) ∧ (∀(i : bv 32%N) (w1 : bv 64%N) (sp1 : ptr (bv 8%N)), length (data sp1) = length (data sp) ∧ offset sp1 = offset sp ∧ min sp1 = min sp ∧ C.max sp1 = C.max sp ∧ writable sp1 = writable sp ∧ zone1 sp1 = zone1 sp -> (0%Z ≤ bv_unsigned w1 ∧ bv_unsigned w1 < 18446744073709551615%Z + 1%Z) ∧ (0%Z ≤ bv_signed i ∧ bv_signed i ≤ bv_signed sz) ∧ (0%Z < bv_unsigned w1 -> 0%Z ≤ bv_signed i ∧ bv_signed i < bv_signed sz) ∧ in_base base (pelts sp1) (offset sp1) (offset sp1 + bv_signed i) ∧ (bv_unsigned w1 = 0%Z -> 0%Z < bv_signed i -> 0%Z < bv_signed (pelts sp1 (offset sp1 + bv_signed i - 1%Z))) ∧ bv_unsigned w = svalue_le base sp1 (bv_signed i) + Z.pow base (bv_signed i) * bv_unsigned w1 ∧ (∀(j : Z), j < offset sp1 ∨ offset sp1 + bv_signed i ≤ j -> pelts sp1 j = pelts sp j) -> (if decide (0%Z < bv_unsigned w1) then uint'64_in_bounds (64%Z - bv_unsigned shift) ∧ (∀(o1 : bv 64%N), bv_unsigned o1 = 64%Z - bv_unsigned shift -> (0%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 < 64%Z) ∧ (∀(h : bv 64%N), bv_unsigned h = ZEuclid.div (bv_unsigned w1) (Z.pow 2%Z (bv_unsigned o1)) -> (0%Z ≤ bv_unsigned shift ∧ bv_unsigned shift < 64%Z) ∧ (∀(l : bv 64%N), bv_unsigned l = ZEuclid.modulo (bv_unsigned w1 * Z.pow 2%Z (bv_unsigned shift)) (18446744073709551615%Z + 1%Z) -> (ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned d1 ∧ bv_unsigned h < bv_unsigned d1 ∧ reciprocal di d1) ∧ (∀(q : bv 64%N) (r : bv 64%N), bv_unsigned q * bv_unsigned d1 + bv_unsigned r = bv_unsigned l + (18446744073709551615%Z + 1%Z) * bv_unsigned h ∧ 0%Z ≤ bv_unsigned r ∧ bv_unsigned r < bv_unsigned d1 -> ((0%Z ≤ bv_unsigned shift ∧ bv_unsigned shift < 64%Z) ∧ ZEuclid.modulo (bv_unsigned r) (Z.pow 2%Z (bv_unsigned shift)) = 0%Z) ∧ (∀(nr : bv 64%N), bv_unsigned r = Z.pow 2%Z (bv_unsigned shift) * bv_unsigned nr -> ((0%Z ≤ bv_unsigned shift ∧ bv_unsigned shift < 64%Z) ∧ ZEuclid.modulo (bv_unsigned r) (Z.pow 2%Z (bv_unsigned shift)) = 0%Z) ∧ (∀(o2 : bv 64%N), bv_unsigned r = Z.pow 2%Z (bv_unsigned shift) * bv_unsigned o2 -> (0%Z ≤ bv_unsigned o2 ∧ bv_unsigned o2 ≤ 255%Z) ∧ (∀(o3 : bv 8%N), bv_signed o3 = bv_unsigned o2 -> ((min sp1 ≤ offset sp1 + bv_signed i ∧ offset sp1 + bv_signed i < C.max sp1) ∧ writable sp1 = true) ∧ (∀(sp2 : ptr (bv 8%N)), length (data sp2) = length (data sp1) ∧ offset sp2 = offset sp1 ∧ min sp2 = min sp1 ∧ C.max sp2 = C.max sp1 ∧ writable sp2 = writable sp1 ∧ zone1 sp2 = zone1 sp1 -> pelts sp2 = fun_updt (pelts sp1) (offset sp2 + bv_signed i) o3 ∧ pelts sp2 (offset sp2 + bv_signed i) = o3 -> int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o4 : bv 32%N), bv_signed o4 = bv_signed i + 1%Z -> bv_unsigned q < bv_unsigned w1 ∧ (0%Z ≤ bv_unsigned q ∧ bv_unsigned q < 18446744073709551615%Z + 1%Z) ∧ (0%Z ≤ bv_signed o4 ∧ bv_signed o4 ≤ bv_signed sz) ∧ (0%Z < bv_unsigned q -> 0%Z ≤ bv_signed o4 ∧ bv_signed o4 < bv_signed sz) ∧ in_base base (pelts sp2) (offset sp2) (offset sp2 + bv_signed o4) ∧ (bv_unsigned q = 0%Z -> 0%Z < bv_signed o4 -> 0%Z < bv_signed (pelts sp2 (offset sp2 + bv_signed o4 - 1%Z))) ∧ bv_unsigned w = svalue_le base sp2 (bv_signed o4) + Z.pow base (bv_signed o4) * bv_unsigned q ∧ (∀(j : Z), j < offset sp2 ∨ offset sp2 + bv_signed o4 ≤ j -> pelts sp2 j = pelts sp j)))))))))) else 0%Z ≤ bv_signed i ∧ (∀(result : bv 32%N), bv_unsigned result = bv_signed i -> svalue_le (b binfo) sp1 (bv_unsigned result) = bv_unsigned w ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result ≤ bv_signed sz) ∧ (0%Z < bv_unsigned result -> 0%Z < bv_signed (pelts sp1 (offset sp1 + bv_unsigned result - 1%Z))) ∧ (∀(i1 : Z), i1 < offset sp1 ∨ offset sp1 + bv_unsigned result ≤ i1 -> pelts sp1 i1 = pelts sp i1) ∧ in_base (b binfo) (pelts sp1) (offset sp1) (offset sp1 + bv_unsigned result)))).
Admitted.
