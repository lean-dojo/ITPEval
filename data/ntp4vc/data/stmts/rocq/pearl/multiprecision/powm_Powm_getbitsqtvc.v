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
Theorem getbits'vc (nbits : bv 32%N) (bi : bv 32%N) (pn : bv 32%N) (p : ptr (bv 64%N)) (fact0 : 1%Z ≤ bv_signed nbits) (fact1 : bv_signed nbits < 64%Z) (fact2 : 0%Z ≤ bv_signed bi) (fact3 : 1%Z ≤ bv_signed pn) (fact4 : valid p (bv_signed pn)) (fact5 : ZEuclid.div (bv_signed bi + 63%Z) 64%Z ≤ bv_signed pn) : if decide (bv_signed bi < bv_signed nbits) then 0%Z ≤ bv_signed bi ∧ (∀(o1 : bv 64%N), bv_unsigned o1 = bv_signed bi -> ((0%Z ≤ bv_unsigned o1 ∧ bv_unsigned o1 < 64%Z) ∧ Z.pow 2%Z (bv_unsigned o1) * bv_unsigned (1%bv : bv 64%N) ≤ 18446744073709551615%Z) ∧ (∀(o2 : bv 64%N), bv_unsigned o2 = Z.pow 2%Z (bv_unsigned o1) * bv_unsigned (1%bv : bv 64%N) -> (min p ≤ offset p ∧ offset p < C.max p) ∧ (let o3 : bv 64%N := pelts p (offset p) in (¬ bv_unsigned o2 = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned o3) (bv_unsigned o2))) ∧ (∀(result : bv 64%N), bv_unsigned result = Z.quot (bv_unsigned o3) (bv_unsigned o2) -> (bv_signed nbits ≤ bv_signed bi -> valueb p (bv_signed bi) = valueb p (bv_signed bi - bv_signed nbits) + Z.pow 2%Z (bv_signed bi - bv_signed nbits) * bv_unsigned result) ∧ (bv_signed bi < bv_signed nbits -> valueb p (bv_signed bi) = bv_unsigned result) ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result < Z.pow 2%Z (bv_signed nbits)) ∧ bv_unsigned result = ZEuclid.modulo (ZEuclid.div (value p (bv_signed pn)) (Z.pow 2%Z (bv_signed bi - bv_signed nbits))) (Z.pow 2%Z (bv_signed nbits)))))) else int'32_in_bounds (bv_signed bi - bv_signed nbits) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed bi - bv_signed nbits -> (¬ 64%Z = 0%Z ∧ int'32_in_bounds (Z.rem (bv_signed o1) 64%Z)) ∧ (∀(o2 : bv 32%N), bv_signed o2 = Z.rem (bv_signed o1) 64%Z -> (¬ 64%Z = 0%Z ∧ int'32_in_bounds (Z.quot (bv_signed o1) 64%Z)) ∧ (∀(o3 : bv 32%N), bv_signed o3 = Z.quot (bv_signed o1) 64%Z -> (min p ≤ offset p + bv_signed o2 ∧ offset p + bv_signed o2 < C.max p) ∧ int'32_in_bounds (bv_signed o2 + 1%Z) ∧ (∀(o4 : bv 32%N), bv_signed o4 = bv_signed o2 + 1%Z -> (min p ≤ offset p + bv_signed o4 ∧ offset p + bv_signed o4 ≤ C.max p) ∧ (∀(p' : ptr (bv 64%N)), offset p' = offset p + bv_signed o4 ∧ plength p' = plength p ∧ pelts p' = pelts p ∧ data p' = data p ∧ min p' = min p ∧ C.max p' = C.max p ∧ zone1 p' = zone1 p ∧ writable p' = writable p -> 0%Z ≤ bv_signed o3 ∧ (∀(o5 : bv 64%N), bv_unsigned o5 = bv_signed o3 -> (0%Z ≤ bv_unsigned o5 ∧ bv_unsigned o5 < 64%Z) ∧ (∀(o6 : bv 64%N), bv_unsigned o6 = ZEuclid.div (bv_unsigned (pelts p (offset p + bv_signed o2))) (Z.pow 2%Z (bv_unsigned o5)) -> ¬ Z.pow 2%Z (bv_signed o3) = 0%Z ∧ int'32_in_bounds (64%Z - bv_signed o3) ∧ (∀(nbits_in_r : bv 32%N), bv_signed nbits_in_r = 64%Z - bv_signed o3 -> (if decide (bv_signed nbits_in_r < bv_signed nbits) then int'32_in_bounds (bv_signed o2 + 1%Z) ∧ (∀(o7 : bv 32%N), bv_signed o7 = bv_signed o2 + 1%Z -> (min p ≤ offset p + bv_signed o7 ∧ offset p + bv_signed o7 < C.max p) ∧ 0%Z ≤ bv_signed nbits_in_r ∧ (∀(o8 : bv 64%N), bv_unsigned o8 = bv_signed nbits_in_r -> (0%Z ≤ bv_unsigned o8 ∧ bv_unsigned o8 < 64%Z) ∧ (∀(prs : bv 64%N), bv_unsigned prs = ZEuclid.modulo (bv_unsigned (pelts p (offset p + bv_signed o7)) * Z.pow 2%Z (bv_unsigned o8)) (18446744073709551615%Z + 1%Z) ∧ bv_unsigned prs ≤ 18446744073709551615%Z + 1%Z - Z.pow 2%Z (bv_unsigned o8) -> int'32_in_bounds (bv_signed o2 + 2%Z) ∧ (∀(o9 : bv 32%N), bv_signed o9 = bv_signed o2 + 2%Z -> (min p ≤ offset p + bv_signed o9 ∧ offset p + bv_signed o9 ≤ C.max p) ∧ (∀(p'' : ptr (bv 64%N)), offset p'' = offset p + bv_signed o9 ∧ plength p'' = plength p ∧ pelts p'' = pelts p ∧ data p'' = data p ∧ min p'' = min p ∧ C.max p'' = C.max p ∧ zone1 p'' = zone1 p ∧ writable p'' = writable p -> ¬ 18446744073709551615%Z + 1%Z = 0%Z ∧ uint'64_in_bounds (bv_unsigned o6 + bv_unsigned prs) ∧ (∀(o10 : bv 64%N), bv_unsigned o10 = bv_unsigned o6 + bv_unsigned prs -> 0%Z ≤ bv_signed nbits ∧ (∀(o11 : bv 64%N), bv_unsigned o11 = bv_signed nbits -> ((0%Z ≤ bv_unsigned o11 ∧ bv_unsigned o11 < 64%Z) ∧ Z.pow 2%Z (bv_unsigned o11) * bv_unsigned (1%bv : bv 64%N) ≤ 18446744073709551615%Z) ∧ (∀(o12 : bv 64%N), bv_unsigned o12 = Z.pow 2%Z (bv_unsigned o11) * bv_unsigned (1%bv : bv 64%N) -> (¬ bv_unsigned o12 = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned o10) (bv_unsigned o12))) ∧ (∀(result : bv 64%N), bv_unsigned result = Z.quot (bv_unsigned o10) (bv_unsigned o12) -> (bv_signed nbits ≤ bv_signed bi -> valueb p (bv_signed bi) = valueb p (bv_signed bi - bv_signed nbits) + Z.pow 2%Z (bv_signed bi - bv_signed nbits) * bv_unsigned result) ∧ (bv_signed bi < bv_signed nbits -> valueb p (bv_signed bi) = bv_unsigned result) ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result < Z.pow 2%Z (bv_signed nbits)) ∧ bv_unsigned result = ZEuclid.modulo (ZEuclid.div (value p (bv_signed pn)) (Z.pow 2%Z (bv_signed bi - bv_signed nbits))) (Z.pow 2%Z (bv_signed nbits))))))))))) else 0%Z ≤ bv_signed nbits ∧ (∀(o7 : bv 64%N), bv_unsigned o7 = bv_signed nbits -> ((0%Z ≤ bv_unsigned o7 ∧ bv_unsigned o7 < 64%Z) ∧ Z.pow 2%Z (bv_unsigned o7) * bv_unsigned (1%bv : bv 64%N) ≤ 18446744073709551615%Z) ∧ (∀(o8 : bv 64%N), bv_unsigned o8 = Z.pow 2%Z (bv_unsigned o7) * bv_unsigned (1%bv : bv 64%N) -> (¬ bv_unsigned o8 = 0%Z ∧ uint'64_in_bounds (Z.quot (bv_unsigned o6) (bv_unsigned o8))) ∧ (∀(result : bv 64%N), bv_unsigned result = Z.quot (bv_unsigned o6) (bv_unsigned o8) -> (bv_signed nbits ≤ bv_signed bi -> valueb p (bv_signed bi) = valueb p (bv_signed bi - bv_signed nbits) + Z.pow 2%Z (bv_signed bi - bv_signed nbits) * bv_unsigned result) ∧ (bv_signed bi < bv_signed nbits -> valueb p (bv_signed bi) = bv_unsigned result) ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result < Z.pow 2%Z (bv_signed nbits)) ∧ bv_unsigned result = ZEuclid.modulo (ZEuclid.div (value p (bv_signed pn)) (Z.pow 2%Z (bv_signed bi - bv_signed nbits))) (Z.pow 2%Z (bv_signed nbits)))))))))))))).
Admitted.
