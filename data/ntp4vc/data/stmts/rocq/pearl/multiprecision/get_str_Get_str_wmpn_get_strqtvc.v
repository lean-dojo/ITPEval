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
Theorem wmpn_get_str'vc (sz : bv 32%N) (un : bv 32%N) (sp : ptr (bv 8%N)) (up : ptr (bv 64%N)) (base : bv 32%N) (fact0 : 0%Z < bv_signed sz) (fact1 : 0%Z < bv_signed un) (fact2 : valid sp (bv_signed sz)) (fact3 : valid up (bv_signed un)) (fact4 : writable sp = true) (fact5 : writable up = true) (fact6 : Z.pow (18446744073709551615%Z + 1%Z) (bv_signed un) ≤ Z.pow (bv_signed base) (bv_signed sz - 1%Z)) (fact7 : 0%Z < bv_unsigned (pelts up (offset up + bv_signed un - 1%Z))) (fact8 : 2%Z ≤ bv_signed base) (fact9 : bv_signed base ≤ 256%Z) (fact10 : 64%Z * bv_signed un + 7%Z ≤ 2147483647%Z) : 0%Z ≤ bv_signed base ∧ (∀(o1 : bv 64%N), bv_unsigned o1 = bv_signed base -> (2%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 ≤ 256%Z) ∧ (∀(bits : bv 32%N), (0%Z ≤ bv_unsigned bits ∧ bv_unsigned bits ≤ 8%Z) ∧ (¬ bv_unsigned bits = 0%Z -> Z.pow 2%Z (bv_unsigned bits) = bv_unsigned o1) ∧ (bv_unsigned bits = 0%Z -> (∀(n : Z), 0%Z ≤ n -> ¬ Z.pow 2%Z n = bv_unsigned o1)) -> (bv_unsigned bits = 0%Z -> bits = (0%bv : bv 32%N)) -> (if decide (¬ bits = (0%bv : bv 32%N)) then int'32_in_bounds (64%Z * bv_signed un) ∧ (∀(o2 : bv 32%N), bv_signed o2 = 64%Z * bv_signed un -> (1%Z ≤ bv_signed un ∧ valid up (bv_signed un) ∧ (1%Z ≤ bv_unsigned bits ∧ bv_unsigned bits ≤ 8%Z) ∧ valid sp (ZEuclid.div (bv_signed o2 + bv_unsigned bits - 1%Z) (bv_unsigned bits)) ∧ 0%Z ≤ bv_signed o2 ∧ value up (bv_signed un) < Z.pow 2%Z (bv_signed o2) ∧ 0%Z < bv_unsigned (pelts up (offset up + bv_signed un - 1%Z)) ∧ 64%Z * bv_signed un + 7%Z ≤ 2147483647%Z ∧ writable sp = true) ∧ (∀(sp1 : ptr (bv 8%N)), length (data sp1) = length (data sp) ∧ offset sp1 = offset sp ∧ min sp1 = min sp ∧ C.max sp1 = C.max sp ∧ writable sp1 = writable sp ∧ zone1 sp1 = zone1 sp -> (∀(result : bv 32%N), in_base (Z.pow 2%Z (bv_unsigned bits)) (pelts sp1) (offset sp1) (offset sp1 + bv_unsigned result) ∧ svalue (Z.pow 2%Z (bv_unsigned bits)) sp1 (bv_unsigned result) = value up (bv_signed un) ∧ (0%Z < bv_unsigned result ∧ bv_unsigned result ≤ ZEuclid.div (bv_signed o2 + bv_unsigned bits - 1%Z) (bv_unsigned bits)) ∧ 0%Z < bv_signed (pelts sp1 (offset sp1)) ∧ (∀(j : Z), j < offset sp1 ∨ offset sp1 + ZEuclid.div (bv_signed o2 + bv_unsigned bits - 1%Z) (bv_unsigned bits) ≤ j -> pelts sp1 j = pelts sp j) -> in_base (bv_signed base) (pelts sp1) (offset sp1) (offset sp1 + bv_unsigned result) ∧ svalue (bv_signed base) sp1 (bv_unsigned result) = value up (bv_signed un) ∧ (0%Z < bv_unsigned result ∧ bv_unsigned result < bv_signed sz) ∧ 0%Z < bv_signed (pelts sp1 (offset sp1))))) else 0%Z ≤ bv_signed base ∧ (∀(o2 : bv 64%N), bv_unsigned o2 = bv_signed base -> (2%Z ≤ bv_unsigned o2 ∧ bv_unsigned o2 ≤ 256%Z) ∧ (∀(info : wmpn_base_info), b info = bv_unsigned o2 -> (valid up (bv_signed un) ∧ 1%Z ≤ bv_signed un ∧ b info = bv_signed base ∧ writable up = true ∧ writable sp = true ∧ 0%Z < bv_unsigned (pelts up (offset up + bv_signed un - 1%Z)) ∧ 0%Z < bv_signed sz ∧ valid sp (bv_signed sz) ∧ value up (bv_signed un) < Z.pow (bv_signed base) (bv_signed sz - 1%Z)) ∧ (∀(sp1 : ptr (bv 8%N)), length (data sp1) = length (data sp) ∧ offset sp1 = offset sp ∧ min sp1 = min sp ∧ C.max sp1 = C.max sp ∧ writable sp1 = writable sp ∧ zone1 sp1 = zone1 sp -> (∀(result : bv 32%N), (0%Z ≤ bv_unsigned result ∧ bv_unsigned result < bv_signed sz) ∧ svalue (bv_signed base) sp1 (bv_unsigned result) = value up (bv_signed un) ∧ in_base (bv_signed base) (pelts sp1) (offset sp1) (offset sp1 + bv_unsigned result) ∧ 0%Z < bv_signed (pelts sp1 (offset sp1)) ∧ (∀(j : Z), j < offset sp1 ∨ offset sp1 + bv_signed sz ≤ j -> pelts sp1 j = pelts sp j) -> in_base (bv_signed base) (pelts sp1) (offset sp1) (offset sp1 + bv_unsigned result) ∧ svalue (bv_signed base) sp1 (bv_unsigned result) = value up (bv_signed un) ∧ (0%Z < bv_unsigned result ∧ bv_unsigned result < bv_signed sz) ∧ 0%Z < bv_signed (pelts sp1 (offset sp1))))))))).
Admitted.
