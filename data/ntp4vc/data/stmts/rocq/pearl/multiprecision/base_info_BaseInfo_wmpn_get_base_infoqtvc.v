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
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import Why3.mach.c.C.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.logical.LogicalUtil.
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.logical.Logical.
Require Import multiprecision.ptralias.Alias.
Open Scope Z_scope.
Axiom wmpn_base_info : Type.
Axiom wmpn_base_info_inhabited : Inhabited wmpn_base_info.
Global Existing Instance wmpn_base_info_inhabited.
Axiom wmpn_base_info_countable : Countable wmpn_base_info.
Global Existing Instance wmpn_base_info_countable.
Axiom b : wmpn_base_info -> Z.
Axiom exp : wmpn_base_info -> bv 32%N.
Axiom bb : wmpn_base_info -> bv 64%N.
Axiom wmpn_base_info'invariant : forall  (self : wmpn_base_info), 2%Z ≤ b self ∧ b self ≤ 256%Z ∧ bv_unsigned (bb self) < 18446744073709551615%Z + 1%Z ∧ 18446744073709551615%Z + 1%Z ≤ bv_unsigned (bb self) * b self ∧ 7%Z ≤ bv_unsigned (exp self) ∧ bv_unsigned (exp self) ≤ 63%Z ∧ bv_unsigned (bb self) = Z.pow (b self) (bv_unsigned (exp self)).
Definition wmpn_base_info'eq (a : wmpn_base_info) (b1 : wmpn_base_info) := b a = b b1 ∧ exp a = exp b1 ∧ bb a = bb b1.
Axiom wmpn_base_info'inj : forall  (a : wmpn_base_info) (b1 : wmpn_base_info) (fact0 : wmpn_base_info'eq a b1), a = b1.
Theorem wmpn_get_base_info'vc (b1 : bv 64%N) (fact0 : 2%Z ≤ bv_unsigned b1) (fact1 : bv_unsigned b1 ≤ 256%Z) : ¬ bv_unsigned b1 = 0%Z ∧ uint'64_in_bounds (Z.rem 18446744073709551615%Z (bv_unsigned b1)) ∧ (∀(m : bv 64%N), bv_unsigned m = Z.rem 18446744073709551615%Z (bv_unsigned b1) -> (Z.pow (bv_unsigned b1) 1%Z = bv_unsigned b1 ∧ 1%Z ≤ 1%Z ∧ 1%Z ≤ 64%Z) ∧ (∀(exp1 : bv 32%N) (p : bv 64%N), Z.pow (bv_unsigned b1) (bv_unsigned exp1) = bv_unsigned p ∧ 1%Z ≤ bv_unsigned exp1 ∧ bv_unsigned exp1 ≤ 64%Z -> (if decide (bv_unsigned p ≤ bv_unsigned m) then uint'64_in_bounds (bv_unsigned p * bv_unsigned b1) ∧ (∀(o1 : bv 64%N), bv_unsigned o1 = bv_unsigned p * bv_unsigned b1 -> uint'32_in_bounds (bv_unsigned exp1 + 1%Z) ∧ (∀(o2 : bv 32%N), bv_unsigned o2 = bv_unsigned exp1 + 1%Z -> (0%Z ≤ bv_unsigned m - bv_unsigned p ∧ bv_unsigned m - bv_unsigned o1 < bv_unsigned m - bv_unsigned p) ∧ Z.pow (bv_unsigned b1) (bv_unsigned o2) = bv_unsigned o1 ∧ 1%Z ≤ bv_unsigned o2 ∧ bv_unsigned o2 ≤ 64%Z)) else let o1 : Z := bv_unsigned b1 in ((2%Z ≤ o1 ∧ o1 ≤ 256%Z) ∧ (bv_unsigned p < 18446744073709551615%Z + 1%Z ∧ 18446744073709551615%Z + 1%Z ≤ bv_unsigned p * o1) ∧ (7%Z ≤ bv_unsigned exp1 ∧ bv_unsigned exp1 ≤ 63%Z) ∧ bv_unsigned p = Z.pow o1 (bv_unsigned exp1)) ∧ (∀(result : wmpn_base_info), b result = o1 ∧ exp result = exp1 ∧ bb result = p -> b result = bv_unsigned b1)))).
Admitted.
