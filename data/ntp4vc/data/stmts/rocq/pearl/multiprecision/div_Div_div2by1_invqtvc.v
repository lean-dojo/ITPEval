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
Require Import multiprecision.ptralias.Alias.
Require Import multiprecision.util.UtilOld.
Require Import multiprecision.add.AddOld.
Require Import multiprecision.sub.SubOld.
Require Import multiprecision.logical.LogicalUtil.
Require Import multiprecision.logical.LogicalOld.
Open Scope Z_scope.
Definition reciprocal (v : bv 64%N) (d : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned d) - (18446744073709551615%Z + 1%Z).
Theorem div2by1_inv'vc (d : bv 64%N) (uh : bv 64%N) (v : bv 64%N) (l : bv 64%N) (h : bv 64%N) (ul : bv 64%N) (fact0 : ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned d) (fact1 : bv_unsigned uh < bv_unsigned d) (fact2 : reciprocal v d) (fact3 : bv_unsigned l + (18446744073709551615%Z + 1%Z) * bv_unsigned h = bv_unsigned v * bv_unsigned uh) : 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ (∀(sl : bv 64%N) (c : bv 64%N), bv_unsigned sl + (18446744073709551615%Z + 1%Z) * bv_unsigned c = bv_unsigned l + bv_unsigned ul + 0%Z ∧ 0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z -> (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(sh : bv 64%N) (c' : bv 64%N), bv_unsigned sh + (18446744073709551615%Z + 1%Z) * bv_unsigned c' = bv_unsigned uh + bv_unsigned h + bv_unsigned c ∧ 0%Z ≤ bv_unsigned c' ∧ bv_unsigned c' ≤ 1%Z -> (∀(o1 : bv 64%N), bv_unsigned o1 = ZEuclid.modulo (bv_unsigned sh + 1%Z) (18446744073709551615%Z + 1%Z) -> (∀(p : bv 64%N), bv_unsigned p = ZEuclid.modulo (bv_unsigned o1 * bv_unsigned d) (18446744073709551615%Z + 1%Z) -> (∀(o2 : bv 64%N), bv_unsigned o2 = ZEuclid.modulo (bv_unsigned ul - bv_unsigned p) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned sl < bv_unsigned o2) then ∀(o3 : bv 64%N), bv_unsigned o3 = ZEuclid.modulo (bv_unsigned o1 - 1%Z) (18446744073709551615%Z + 1%Z) -> (∀(o4 : bv 64%N), bv_unsigned o4 = ZEuclid.modulo (bv_unsigned o2 + bv_unsigned d) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned d ≤ bv_unsigned o4) then uint'64_in_bounds (bv_unsigned o3 + 1%Z) ∧ (∀(o5 : bv 64%N), bv_unsigned o5 = bv_unsigned o3 + 1%Z -> uint'64_in_bounds (bv_unsigned o4 - bv_unsigned d) ∧ (∀(o6 : bv 64%N), bv_unsigned o6 = bv_unsigned o4 - bv_unsigned d -> bv_unsigned o5 * bv_unsigned d + bv_unsigned o6 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned o6 ∧ bv_unsigned o6 < bv_unsigned d)) else bv_unsigned o3 * bv_unsigned d + bv_unsigned o4 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned o4 ∧ bv_unsigned o4 < bv_unsigned d)) else if decide (bv_unsigned d ≤ bv_unsigned o2) then uint'64_in_bounds (bv_unsigned o1 + 1%Z) ∧ (∀(o3 : bv 64%N), bv_unsigned o3 = bv_unsigned o1 + 1%Z -> uint'64_in_bounds (bv_unsigned o2 - bv_unsigned d) ∧ (∀(o4 : bv 64%N), bv_unsigned o4 = bv_unsigned o2 - bv_unsigned d -> bv_unsigned o3 * bv_unsigned d + bv_unsigned o4 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned o4 ∧ bv_unsigned o4 < bv_unsigned d)) else bv_unsigned o1 * bv_unsigned d + bv_unsigned o2 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned o2 ∧ bv_unsigned o2 < bv_unsigned d)))))).
Admitted.
