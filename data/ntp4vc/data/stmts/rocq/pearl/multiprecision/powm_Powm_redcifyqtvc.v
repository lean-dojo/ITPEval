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
Theorem redcify'vc (rp : ptr (bv 64%N)) (n : bv 32%N) (up : ptr (bv 64%N)) (un : bv 32%N) (mp : ptr (bv 64%N)) (fact0 : valid rp (bv_signed n)) (fact1 : valid up (bv_signed un)) (fact2 : valid mp (bv_signed n)) (fact3 : 1%Z ≤ bv_signed n) (fact4 : 1%Z ≤ bv_signed un) (fact5 : bv_signed un + bv_signed n < 2147483647%Z) (fact6 : 0%Z < bv_unsigned (pelts mp (offset mp + bv_signed n - 1%Z))) (fact7 : writable rp = true) : int'32_in_bounds (bv_signed un + bv_signed n) ∧ (∀(o1 : bv 32%N), bv_signed o1 = bv_signed un + bv_signed n -> 0%Z ≤ bv_signed o1 ∧ (∀(o2 : bv 32%N), bv_unsigned o2 = bv_signed o1 -> 0%Z ≤ bv_unsigned o2 ∧ (∀(tp : ptr (bv 64%N)), plength tp = bv_unsigned o2 ∧ offset tp = 0%Z ∧ min tp = 0%Z ∧ C.max tp = bv_unsigned o2 ∧ writable tp = true -> int'32_in_bounds (bv_signed un + 1%Z) ∧ (∀(o3 : bv 32%N), bv_signed o3 = bv_signed un + 1%Z -> 0%Z ≤ bv_signed o3 ∧ (∀(o4 : bv 32%N), bv_unsigned o4 = bv_signed o3 -> 0%Z ≤ bv_unsigned o4 ∧ (∀(qp : ptr (bv 64%N)), plength qp = bv_unsigned o4 ∧ offset qp = 0%Z ∧ min qp = 0%Z ∧ C.max qp = bv_unsigned o4 ∧ writable qp = true -> (valid tp (bv_signed n) ∧ writable tp = true) ∧ (∀(tp1 : ptr (bv 64%N)), length (data tp1) = length (data tp) ∧ offset tp1 = offset tp ∧ min tp1 = min tp ∧ C.max tp1 = C.max tp ∧ writable tp1 = writable tp ∧ zone1 tp1 = zone1 tp -> value tp1 (bv_signed n) = 0%Z ∧ (∀(j : Z), j < offset tp1 ∨ offset tp1 + bv_signed n ≤ j -> pelts tp1 j = pelts tp j) -> (min tp1 ≤ offset tp1 + bv_signed n ∧ offset tp1 + bv_signed n ≤ C.max tp1) ∧ (∀(o5 : ptr (bv 64%N)), offset o5 = offset tp1 + bv_signed n ∧ plength o5 = plength tp1 ∧ pelts o5 = pelts tp1 ∧ data o5 = data tp1 ∧ min o5 = min tp1 ∧ C.max o5 = C.max tp1 ∧ zone1 o5 = zone1 tp1 ∧ writable o5 = writable tp1 -> (valid up (bv_signed un) ∧ valid o5 (bv_signed un) ∧ writable o5 = true) ∧ (∀(o6 : ptr (bv 64%N)) (tp2 : ptr (bv 64%N)), data o6 = data tp2 ∧ length (data tp2) = length (data o5) ∧ offset o6 = offset o5 ∧ min o6 = min o5 ∧ C.max o6 = C.max o5 ∧ writable o6 = writable o5 ∧ zone1 o6 = zone1 o5 -> length (data tp2) = length (data tp1) ∧ offset tp2 = offset tp1 ∧ min tp2 = min tp1 ∧ C.max tp2 = C.max tp1 ∧ writable tp2 = writable tp1 ∧ zone1 tp2 = zone1 tp1 -> map_eq_sub_shift (pelts o6) (pelts up) (offset o6) (offset up) (bv_signed un) ∧ (∀(j : Z), j < offset o6 ∨ offset o6 + bv_signed un ≤ j -> pelts o6 j = pelts o5 j) -> int'32_in_bounds (bv_signed un + bv_signed n) ∧ (∀(o7 : bv 32%N), bv_signed o7 = bv_signed un + bv_signed n -> ((1%Z ≤ bv_signed n ∧ bv_signed n ≤ bv_signed o7 ∧ bv_signed o7 ≤ 2147483647%Z - 1%Z) ∧ valid tp2 (bv_signed o7) ∧ valid mp (bv_signed n) ∧ valid qp (bv_signed o7 - bv_signed n + 1%Z) ∧ valid rp (bv_signed n) ∧ (writable qp = true ∧ writable rp = true) ∧ 0%Z < bv_unsigned (pelts mp (offset mp + bv_signed n - 1%Z))) ∧ (∀(qp1 : ptr (bv 64%N)) (rp1 : ptr (bv 64%N)), length (data qp1) = length (data qp) ∧ offset qp1 = offset qp ∧ min qp1 = min qp ∧ C.max qp1 = C.max qp ∧ writable qp1 = writable qp ∧ zone1 qp1 = zone1 qp -> length (data rp1) = length (data rp) ∧ offset rp1 = offset rp ∧ min rp1 = min rp ∧ C.max rp1 = C.max rp ∧ writable rp1 = writable rp ∧ zone1 rp1 = zone1 rp -> value tp2 (bv_signed o7) = value qp1 (bv_signed o7 - bv_signed n + 1%Z) * value mp (bv_signed n) + value rp1 (bv_signed n) ∧ value rp1 (bv_signed n) < value mp (bv_signed n) -> value rp1 (bv_signed n) = ZEuclid.modulo (Z.pow (18446744073709551615%Z + 1%Z) (bv_signed n) * value up (bv_signed un)) (value mp (bv_signed n)) ∧ redc (value rp1 (bv_signed n)) (value up (bv_signed un)) (bv_signed n) (value mp (bv_signed n))))))))))))).
Admitted.
