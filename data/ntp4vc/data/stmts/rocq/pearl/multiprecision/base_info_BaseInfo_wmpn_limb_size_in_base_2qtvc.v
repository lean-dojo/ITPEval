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
Theorem wmpn_limb_size_in_base_2'vc (u : bv 64%N) (fact0 : 0%Z < bv_unsigned u) : 0%Z < bv_unsigned u ∧ (∀(o1 : bv 32%N), Z.pow 2%Z (bv_signed o1) * bv_unsigned u ≤ 18446744073709551615%Z ∧ 18446744073709551615%Z < 2%Z * Z.pow 2%Z (bv_signed o1) * bv_unsigned u ∧ 0%Z ≤ bv_signed o1 ∧ bv_signed o1 < 64%Z -> 0%Z ≤ bv_signed o1 ∧ (∀(shift : bv 64%N), bv_unsigned shift = bv_signed o1 -> uint'64_in_bounds (64%Z - bv_unsigned shift) ∧ (∀(r : bv 64%N), bv_unsigned r = 64%Z - bv_unsigned shift -> (1%Z ≤ bv_unsigned r ∧ bv_unsigned r ≤ 64%Z) ∧ Z.pow 2%Z (bv_unsigned r - 1%Z) ≤ bv_unsigned u ∧ bv_unsigned u < Z.pow 2%Z (bv_unsigned r)))).
Admitted.
