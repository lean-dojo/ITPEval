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
Require Import multiprecision.lemmas.Lemmas.
Require Import multiprecision.types.Config.
Require Import multiprecision.types.Types.
Require Import multiprecision.types.Int32Eq.
Require Import multiprecision.types.UInt64Eq.
Require Import multiprecision.ptralias.Alias.
Open Scope Z_scope.
Theorem add_n_rxy'vc (sx : bv 32%N) (x : ptr (bv 64%N)) (fact0 : 0%Z ≤ bv_signed sx) (fact1 : writable x = true) (fact2 : valid x (bv_signed sx)) : 0%Z ≤ bv_signed sx ∧ valid x (bv_signed sx) ∧ writable x = true ∧ (∀(x1 : ptr (bv 64%N)), length (data x1) = length (data x) ∧ offset x1 = offset x ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ writable x1 = writable x ∧ zone1 x1 = zone1 x -> (∀(result : bv 64%N), value x1 (bv_signed sx) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned result = value x (bv_signed sx) + value x (bv_signed sx) ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result ≤ 1%Z) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sx ≤ j -> pelts x1 j = pelts x j) -> value x1 (bv_signed sx) + Z.pow (18446744073709551615%Z + 1%Z) (bv_signed sx) * bv_unsigned result = value x (bv_signed sx) + value x (bv_signed sx) ∧ (0%Z ≤ bv_unsigned result ∧ bv_unsigned result ≤ 1%Z) ∧ (∀(j : Z), j < offset x1 ∨ offset x1 + bv_signed sx ≤ j -> pelts x1 j = pelts x j) ∧ min x1 = min x ∧ C.max x1 = C.max x ∧ plength x1 = plength x)).
Admitted.
