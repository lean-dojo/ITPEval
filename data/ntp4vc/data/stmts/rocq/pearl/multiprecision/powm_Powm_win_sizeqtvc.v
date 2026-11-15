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
Theorem win_size'vc (eb : bv 32%N) (o1 : bool) (result : bv 32%N) (fact0 : bv_signed eb = bv_signed (0%bv : bv 32%N) -> o1 = true) (fact1 : o1 = true -> eb = (0%bv : bv 32%N)) (fact2 : if decide (o1 = true) then result = (0%bv : bv 32%N) else if decide (bv_signed eb ≤ 7%Z) then result = (1%bv : bv 32%N) else if decide (bv_signed eb ≤ 25%Z) then result = (2%bv : bv 32%N) else if decide (bv_signed eb ≤ 81%Z) then result = (3%bv : bv 32%N) else if decide (bv_signed eb ≤ 214%Z) then result = (4%bv : bv 32%N) else if decide (bv_signed eb ≤ 673%Z) then result = (5%bv : bv 32%N) else if decide (bv_signed eb ≤ 1793%Z) then result = (6%bv : bv 32%N) else if decide (bv_signed eb ≤ 4609%Z) then result = (7%bv : bv 32%N) else if decide (bv_signed eb ≤ 11521%Z) then result = (8%bv : bv 32%N) else if decide (bv_signed eb ≤ 28161%Z) then result = (9%bv : bv 32%N) else result = (10%bv : bv 32%N)) : 0%Z ≤ bv_signed result ∧ bv_signed result ≤ 10%Z ∧ (0%Z < bv_signed eb -> 0%Z < bv_signed result).
Admitted.
