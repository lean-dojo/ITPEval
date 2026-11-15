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
Definition valueb (p : ptr (bv 64%N)) (nbits : Z) : Z := if decide (nbits < 0%Z) then 0%Z else let i : Z := ZEuclid.div nbits 64%Z in value p i + Z.pow (18446744073709551615%Z + 1%Z) i * ZEuclid.modulo (bv_unsigned (pelts p (offset p + i))) (Z.pow 2%Z (nbits - 64%Z * i)).
Theorem getbit'vc (p : ptr (bv 64%N)) (pn : bv 32%N) (bi : bv 32%N) (fact0 : valid p (bv_signed pn)) (fact1 : 1%Z ≤ bv_signed bi) (fact2 : ZEuclid.div (bv_signed bi + 63%Z) 64%Z ≤ bv_signed pn) : int'32_in_bounds (bv_signed bi - 1%Z) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed bi - 1%Z -> (¬ 64%Z = 0%Z ∧ int'32_in_bounds (Z.rem (bv_signed o1) 64%Z)) ∧ (∀(i : bv 32%N), bv_signed i = Z.rem (bv_signed o1) 64%Z -> int'32_in_bounds (bv_signed bi - 1%Z) ∧ (∀(o2 : bv 32%N), bv_signed o2 = bv_signed bi - 1%Z -> 0%Z ≤ bv_signed o2 ∧ (∀(o3 : bv 64%N), bv_unsigned o3 = bv_signed o2 -> (¬ 64%Z = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned o3) 64%Z)) ∧ (∀(mi : bv 64%N), bv_unsigned mi = Z.quot (bv_unsigned o3) 64%Z -> (min p ≤ offset p + bv_signed i ∧ offset p + bv_signed i < C.max p) ∧ int'32_in_bounds (bv_signed i + 1%Z) ∧ (∀(o4 : bv 32%N), bv_signed o4 = bv_signed i + 1%Z -> (min p ≤ offset p + bv_signed o4 ∧ offset p + bv_signed o4 ≤ C.max p) ∧ (∀(p' : ptr (bv 64%N)), offset p' = offset p + bv_signed o4 ∧ plength p' = plength p ∧ pelts p' = pelts p ∧ data p' = data p ∧ min p' = min p ∧ C.max p' = C.max p ∧ zone1 p' = zone1 p ∧ writable p' = writable p -> (0%Z ≤ bv_unsigned mi ∧ bv_unsigned mi < 64%Z) ∧ (∀(lps : bv 64%N), bv_unsigned lps = ZEuclid.div (bv_unsigned (pelts p (offset p + bv_signed i))) (Z.pow 2%Z (bv_unsigned mi)) -> ¬ Z.pow 2%Z (bv_unsigned mi) = 0%Z ∧ (¬ 2%Z = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned lps) 2%Z)) ∧ (∀(res : bv 64%N), bv_unsigned res = Z.quot (bv_unsigned lps) 2%Z -> ¬ 2%Z = 0%Z ∧ (¬ 2%Z = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned lps) 2%Z)) ∧ (∀(result : bv 64%N), bv_unsigned result = Z.quot (bv_unsigned lps) 2%Z -> (0%Z ≤ bv_unsigned result ∧ bv_unsigned result ≤ 1%Z) ∧ bv_unsigned result = ZEuclid.modulo (ZEuclid.div (value p (bv_signed pn)) (Z.pow 2%Z (bv_signed bi - 1%Z))) 2%Z ∧ valueb p (bv_signed bi) = valueb p (bv_signed bi - 1%Z) + Z.pow 2%Z (bv_signed bi - 1%Z) * bv_unsigned result)))))))))).
Admitted.
