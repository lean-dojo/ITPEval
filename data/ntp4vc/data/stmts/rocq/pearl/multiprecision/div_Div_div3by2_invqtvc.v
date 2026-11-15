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
Theorem div3by2_inv'vc (dh : bv 64%N) (v : bv 64%N) (dl : bv 64%N) (um : bv 64%N) (uh : bv 64%N) (l : bv 64%N) (h : bv 64%N) (ul : bv 64%N) (fact0 : ZEuclid.div (18446744073709551615%Z + 1%Z) 2%Z ≤ bv_unsigned dh) (fact1 : reciprocal_3by2 v dh dl) (fact2 : bv_unsigned um + (18446744073709551615%Z + 1%Z) * bv_unsigned uh < bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh) (fact3 : bv_unsigned l + (18446744073709551615%Z + 1%Z) * bv_unsigned h = bv_unsigned v * bv_unsigned uh) : 0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z ∧ (∀(sl : bv 64%N) (c : bv 64%N), bv_unsigned sl + (18446744073709551615%Z + 1%Z) * bv_unsigned c = bv_unsigned um + bv_unsigned l + 0%Z ∧ 0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z -> (0%Z ≤ bv_unsigned c ∧ bv_unsigned c ≤ 1%Z) ∧ (∀(sh : bv 64%N) (c' : bv 64%N), bv_unsigned sh + (18446744073709551615%Z + 1%Z) * bv_unsigned c' = bv_unsigned uh + bv_unsigned h + bv_unsigned c ∧ 0%Z ≤ bv_unsigned c' ∧ bv_unsigned c' ≤ 1%Z -> (∀(o1 : bv 64%N), bv_unsigned o1 = ZEuclid.modulo (bv_unsigned sh + 1%Z) (18446744073709551615%Z + 1%Z) -> (∀(p : bv 64%N), bv_unsigned p = ZEuclid.modulo (bv_unsigned dh * bv_unsigned sh) (18446744073709551615%Z + 1%Z) -> (∀(o2 : bv 64%N), bv_unsigned o2 = ZEuclid.modulo (bv_unsigned um - bv_unsigned p) (18446744073709551615%Z + 1%Z) -> ¬ 18446744073709551615%Z + 1%Z = 0%Z ∧ (∀(tl : bv 64%N) (th : bv 64%N), bv_unsigned tl + (18446744073709551615%Z + 1%Z) * bv_unsigned th = bv_unsigned sh * bv_unsigned dl -> (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(il : bv 64%N) (b : bv 64%N), bv_unsigned il - (18446744073709551615%Z + 1%Z) * bv_unsigned b = bv_unsigned ul - bv_unsigned tl - 0%Z ∧ 0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z -> (0%Z ≤ bv_unsigned b ∧ bv_unsigned b ≤ 1%Z) ∧ (∀(ih : bv 64%N) (b' : bv 64%N), bv_unsigned ih - (18446744073709551615%Z + 1%Z) * bv_unsigned b' = bv_unsigned o2 - bv_unsigned th - bv_unsigned b ∧ 0%Z ≤ bv_unsigned b' ∧ bv_unsigned b' ≤ 1%Z -> (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(bl : bv 64%N) (b2 : bv 64%N), bv_unsigned bl - (18446744073709551615%Z + 1%Z) * bv_unsigned b2 = bv_unsigned il - bv_unsigned dl - 0%Z ∧ 0%Z ≤ bv_unsigned b2 ∧ bv_unsigned b2 ≤ 1%Z -> (0%Z ≤ bv_unsigned b2 ∧ bv_unsigned b2 ≤ 1%Z) ∧ (∀(bh : bv 64%N) (b2' : bv 64%N), bv_unsigned bh - (18446744073709551615%Z + 1%Z) * bv_unsigned b2' = bv_unsigned ih - bv_unsigned dh - bv_unsigned b2 ∧ 0%Z ≤ bv_unsigned b2' ∧ bv_unsigned b2' ≤ 1%Z -> (if decide (bv_unsigned sl ≤ bv_unsigned bh) then ∀(o3 : bv 64%N), bv_unsigned o3 = ZEuclid.modulo (bv_unsigned o1 - 1%Z) (18446744073709551615%Z + 1%Z) -> (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(rl : bv 64%N) (c1 : bv 64%N), bv_unsigned rl + (18446744073709551615%Z + 1%Z) * bv_unsigned c1 = bv_unsigned bl + bv_unsigned dl + 0%Z ∧ 0%Z ≤ bv_unsigned c1 ∧ bv_unsigned c1 ≤ 1%Z -> (0%Z ≤ bv_unsigned c1 ∧ bv_unsigned c1 ≤ 1%Z) ∧ (∀(rh : bv 64%N) (c'1 : bv 64%N), bv_unsigned rh + (18446744073709551615%Z + 1%Z) * bv_unsigned c'1 = bv_unsigned bh + bv_unsigned dh + bv_unsigned c1 ∧ 0%Z ≤ bv_unsigned c'1 ∧ bv_unsigned c'1 ≤ 1%Z -> (∀(o4 : bool), (if decide (bv_unsigned dh < bv_unsigned rh) then o4 = true else ∃(o5 : bool), ((bv_unsigned rh = bv_unsigned dh -> o5 = true) ∧ (o5 = true -> rh = dh)) ∧ o4 = (if decide (o5 = true) then if decide (bv_unsigned dl ≤ bv_unsigned rl) then true else false else false)) -> (if decide (o4 = true) then (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(bl1 : bv 64%N) (b1 : bv 64%N), bv_unsigned bl1 - (18446744073709551615%Z + 1%Z) * bv_unsigned b1 = bv_unsigned rl - bv_unsigned dl - 0%Z ∧ 0%Z ≤ bv_unsigned b1 ∧ bv_unsigned b1 ≤ 1%Z -> (0%Z ≤ bv_unsigned b1 ∧ bv_unsigned b1 ≤ 1%Z) ∧ (∀(bh1 : bv 64%N) (b'1 : bv 64%N), bv_unsigned bh1 - (18446744073709551615%Z + 1%Z) * bv_unsigned b'1 = bv_unsigned rh - bv_unsigned dh - bv_unsigned b1 ∧ 0%Z ≤ bv_unsigned b'1 ∧ bv_unsigned b'1 ≤ 1%Z -> (∀(o5 : bv 64%N), bv_unsigned o5 = ZEuclid.modulo (bv_unsigned o3 + 1%Z) (18446744073709551615%Z + 1%Z) -> bv_unsigned o5 * bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned o5 * bv_unsigned dh + bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned um + (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 ∧ bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 < bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh))) else bv_unsigned o3 * bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned o3 * bv_unsigned dh + bv_unsigned rl + (18446744073709551615%Z + 1%Z) * bv_unsigned rh = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned um + (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned rl + (18446744073709551615%Z + 1%Z) * bv_unsigned rh ∧ bv_unsigned rl + (18446744073709551615%Z + 1%Z) * bv_unsigned rh < bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh)))) else ∀(o3 : bool), (if decide (bv_unsigned dh < bv_unsigned bh) then o3 = true else ∃(o4 : bool), ((bv_unsigned bh = bv_unsigned dh -> o4 = true) ∧ (o4 = true -> bh = dh)) ∧ o3 = (if decide (o4 = true) then if decide (bv_unsigned dl ≤ bv_unsigned bl) then true else false else false)) -> (if decide (o3 = true) then (0%Z ≤ 0%Z ∧ 0%Z ≤ 1%Z) ∧ (∀(bl1 : bv 64%N) (b3 : bv 64%N), bv_unsigned bl1 - (18446744073709551615%Z + 1%Z) * bv_unsigned b3 = bv_unsigned bl - bv_unsigned dl - 0%Z ∧ 0%Z ≤ bv_unsigned b3 ∧ bv_unsigned b3 ≤ 1%Z -> (0%Z ≤ bv_unsigned b3 ∧ bv_unsigned b3 ≤ 1%Z) ∧ (∀(bh1 : bv 64%N) (b'1 : bv 64%N), bv_unsigned bh1 - (18446744073709551615%Z + 1%Z) * bv_unsigned b'1 = bv_unsigned bh - bv_unsigned dh - bv_unsigned b3 ∧ 0%Z ≤ bv_unsigned b'1 ∧ bv_unsigned b'1 ≤ 1%Z -> (∀(o4 : bv 64%N), bv_unsigned o4 = ZEuclid.modulo (bv_unsigned o1 + 1%Z) (18446744073709551615%Z + 1%Z) -> bv_unsigned o4 * bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned o4 * bv_unsigned dh + bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned um + (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 ∧ bv_unsigned bl1 + (18446744073709551615%Z + 1%Z) * bv_unsigned bh1 < bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh))) else bv_unsigned o1 * bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned o1 * bv_unsigned dh + bv_unsigned bl + (18446744073709551615%Z + 1%Z) * bv_unsigned bh = bv_unsigned ul + (18446744073709551615%Z + 1%Z) * bv_unsigned um + (18446744073709551615%Z + 1%Z) * (18446744073709551615%Z + 1%Z) * bv_unsigned uh ∧ 0%Z ≤ bv_unsigned bl + (18446744073709551615%Z + 1%Z) * bv_unsigned bh ∧ bv_unsigned bl + (18446744073709551615%Z + 1%Z) * bv_unsigned bh < bv_unsigned dl + (18446744073709551615%Z + 1%Z) * bv_unsigned dh)))))))))))).
Admitted.
