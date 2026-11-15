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
Definition reciprocal_3by2 (v : bv 64%N) (dh : bv 64%N) (dl : bv 64%N) := bv_unsigned v = ZEuclid.div ((18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) - 1%Z) (bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh) - (18446744073709551615%Z + 1%Z).
Theorem reciprocal_word_3by2'vc (dh : bv 64%N) (dl : bv 64%N) (fact0 : ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned dh) : ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned dh ∧ (∀(o1 : bv 64%N), reciprocal o1 dh -> (∀(o2 : bv 64%N), bv_unsigned o2 = ZEuclid.modulo (bv_unsigned dh * bv_unsigned o1) (18446744073709551615%Z + 1%Z) -> (∀(o3 : bv 64%N), bv_unsigned o3 = ZEuclid.modulo (bv_unsigned o2 + bv_unsigned dl) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned o3 < bv_unsigned dl) then if decide (bv_unsigned dh ≤ bv_unsigned o3) then uint'64_in_bounds (bv_unsigned o1 - 1%Z) ∧ (∀(o4 : bv 64%N), bv_unsigned o4 = bv_unsigned o1 - 1%Z -> uint'64_in_bounds (bv_unsigned o3 - bv_unsigned dh) ∧ (∀(o5 : bv 64%N), bv_unsigned o5 = bv_unsigned o3 - bv_unsigned dh -> uint'64_in_bounds (bv_unsigned o4 - 1%Z) ∧ (∀(o6 : bv 64%N), bv_unsigned o6 = bv_unsigned o4 - 1%Z -> (∀(o7 : bv 64%N), bv_unsigned o7 = ZEuclid.modulo (bv_unsigned o5 - bv_unsigned dh) (18446744073709551615%Z + 1%Z) -> (∀(tl : bv 64%N) (th : bv 64%N), bv_unsigned tl + (18446744073709551615%Z + 1%Z) * bv_unsigned th = bv_unsigned o6 * bv_unsigned dl -> (∀(o8 : bv 64%N), bv_unsigned o8 = ZEuclid.modulo (bv_unsigned o7 + bv_unsigned th) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned o8 < bv_unsigned th) then ∀(o9 : bool), (if decide (bv_unsigned dh < bv_unsigned o8) then o9 = true else ∃(o10 : bool), ((bv_unsigned o8 = bv_unsigned dh -> o10 = true) ∧ (o10 = true -> o8 = dh)) ∧ (if decide (o10 = true) then o9 = (if decide (bv_unsigned dl ≤ bv_unsigned tl) then true else false) else o9 = false)) -> (if decide (o9 = true) then uint'64_in_bounds (bv_unsigned o6 - 1%Z) ∧ (∀(o10 : bv 64%N), bv_unsigned o10 = bv_unsigned o6 - 1%Z -> uint'64_in_bounds (bv_unsigned o10 - 1%Z) ∧ (∀(o11 : bv 64%N), bv_unsigned o11 = bv_unsigned o10 - 1%Z -> reciprocal_3by2 o11 dh dl)) else uint'64_in_bounds (bv_unsigned o6 - 1%Z) ∧ (∀(o10 : bv 64%N), bv_unsigned o10 = bv_unsigned o6 - 1%Z -> reciprocal_3by2 o10 dh dl)) else reciprocal_3by2 o6 dh dl))))))) else uint'64_in_bounds (bv_unsigned o1 - 1%Z) ∧ (∀(o4 : bv 64%N), bv_unsigned o4 = bv_unsigned o1 - 1%Z -> (∀(o5 : bv 64%N), bv_unsigned o5 = ZEuclid.modulo (bv_unsigned o3 - bv_unsigned dh) (18446744073709551615%Z + 1%Z) -> (∀(tl : bv 64%N) (th : bv 64%N), bv_unsigned tl + (18446744073709551615%Z + 1%Z) * bv_unsigned th = bv_unsigned o4 * bv_unsigned dl -> (∀(o6 : bv 64%N), bv_unsigned o6 = ZEuclid.modulo (bv_unsigned o5 + bv_unsigned th) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned o6 < bv_unsigned th) then ∀(o7 : bool), (if decide (bv_unsigned dh < bv_unsigned o6) then o7 = true else ∃(o8 : bool), ((bv_unsigned o6 = bv_unsigned dh -> o8 = true) ∧ (o8 = true -> o6 = dh)) ∧ (if decide (o8 = true) then o7 = (if decide (bv_unsigned dl ≤ bv_unsigned tl) then true else false) else o7 = false)) -> (if decide (o7 = true) then uint'64_in_bounds (bv_unsigned o4 - 1%Z) ∧ (∀(o8 : bv 64%N), bv_unsigned o8 = bv_unsigned o4 - 1%Z -> uint'64_in_bounds (bv_unsigned o8 - 1%Z) ∧ (∀(o9 : bv 64%N), bv_unsigned o9 = bv_unsigned o8 - 1%Z -> reciprocal_3by2 o9 dh dl)) else uint'64_in_bounds (bv_unsigned o4 - 1%Z) ∧ (∀(o8 : bv 64%N), bv_unsigned o8 = bv_unsigned o4 - 1%Z -> reciprocal_3by2 o8 dh dl)) else reciprocal_3by2 o4 dh dl))))) else ∀(tl : bv 64%N) (th : bv 64%N), bv_unsigned tl + (18446744073709551615%Z + 1%Z) * bv_unsigned th = bv_unsigned o1 * bv_unsigned dl -> (∀(o4 : bv 64%N), bv_unsigned o4 = ZEuclid.modulo (bv_unsigned o3 + bv_unsigned th) (18446744073709551615%Z + 1%Z) -> (if decide (bv_unsigned o4 < bv_unsigned th) then ∀(o5 : bool), (if decide (bv_unsigned dh < bv_unsigned o4) then o5 = true else ∃(o6 : bool), ((bv_unsigned o4 = bv_unsigned dh -> o6 = true) ∧ (o6 = true -> o4 = dh)) ∧ (if decide (o6 = true) then o5 = (if decide (bv_unsigned dl ≤ bv_unsigned tl) then true else false) else o5 = false)) -> (if decide (o5 = true) then uint'64_in_bounds (bv_unsigned o1 - 1%Z) ∧ (∀(o6 : bv 64%N), bv_unsigned o6 = bv_unsigned o1 - 1%Z -> uint'64_in_bounds (bv_unsigned o6 - 1%Z) ∧ (∀(o7 : bv 64%N), bv_unsigned o7 = bv_unsigned o6 - 1%Z -> reciprocal_3by2 o7 dh dl)) else uint'64_in_bounds (bv_unsigned o1 - 1%Z) ∧ (∀(o6 : bv 64%N), bv_unsigned o6 = bv_unsigned o1 - 1%Z -> reciprocal_3by2 o6 dh dl)) else reciprocal_3by2 o1 dh dl)))))).
Admitted.
