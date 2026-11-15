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
Theorem wmpn_base_power_of_two_p'vc (b : bv 64%N) (o1 : bool) (result : bv 32%N) (fact0 : 2%Z ≤ bv_unsigned b) (fact1 : bv_unsigned b ≤ 256%Z) (fact2 : bv_unsigned b = bv_unsigned (2%bv : bv 64%N) -> o1 = true) (fact3 : o1 = true -> b = (2%bv : bv 64%N)) (fact4 : if decide (o1 = true) then result = (1%bv : bv 32%N) else ∃(o2 : bool), ((bv_unsigned b = bv_unsigned (4%bv : bv 64%N) -> o2 = true) ∧ (o2 = true -> b = (4%bv : bv 64%N))) ∧ (if decide (o2 = true) then result = (2%bv : bv 32%N) else ∃(o3 : bool), ((bv_unsigned b = bv_unsigned (8%bv : bv 64%N) -> o3 = true) ∧ (o3 = true -> b = (8%bv : bv 64%N))) ∧ (if decide (o3 = true) then result = (3%bv : bv 32%N) else ∃(o4 : bool), ((bv_unsigned b = bv_unsigned (16%bv : bv 64%N) -> o4 = true) ∧ (o4 = true -> b = (16%bv : bv 64%N))) ∧ (if decide (o4 = true) then result = (4%bv : bv 32%N) else ∃(o5 : bool), ((bv_unsigned b = bv_unsigned (32%bv : bv 64%N) -> o5 = true) ∧ (o5 = true -> b = (32%bv : bv 64%N))) ∧ (if decide (o5 = true) then result = (5%bv : bv 32%N) else ∃(o6 : bool), ((bv_unsigned b = bv_unsigned (64%bv : bv 64%N) -> o6 = true) ∧ (o6 = true -> b = (64%bv : bv 64%N))) ∧ (if decide (o6 = true) then result = (6%bv : bv 32%N) else ∃(o7 : bool), ((bv_unsigned b = bv_unsigned (128%bv : bv 64%N) -> o7 = true) ∧ (o7 = true -> b = (128%bv : bv 64%N))) ∧ (if decide (o7 = true) then result = (7%bv : bv 32%N) else ∃(o8 : bool), ((bv_unsigned b = bv_unsigned (256%bv : bv 64%N) -> o8 = true) ∧ (o8 = true -> b = (256%bv : bv 64%N))) ∧ (if decide (o8 = true) then result = (8%bv : bv 32%N) else result = (0%bv : bv 32%N))))))))) : 0%Z ≤ bv_unsigned result ∧ bv_unsigned result ≤ 8%Z ∧ (¬ bv_unsigned result = 0%Z -> Z.pow 2%Z (bv_unsigned result) = bv_unsigned b) ∧ (bv_unsigned result = 0%Z -> (∀(n : Z), 0%Z ≤ n -> ¬ Z.pow 2%Z n = bv_unsigned b)).
Admitted.
