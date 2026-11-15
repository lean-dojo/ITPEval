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
Require Import Why3.why3.WellFounded.WellFounded.
Require Import Why3.why3.Ref.Ref.
Require Import Why3.mach.bv.BVCheck8.
Require Import Why3.mach.bv.BVCheck32.
Require Import Why3.mach.bv.BVCheck64.
Open Scope Z_scope.
Definition nth8_stream (stream : list (bv 8%N)) (pos : Z) : bool := Z.testbit (bv_unsigned (nth (Z.to_nat (ZEuclid.div pos 8%Z)) stream inhabitant)) (7%Z - ZEuclid.modulo pos 8%Z).
Definition maxvalue (len : bv 32%N) : bv 64%N := bv_shiftl (1%bv : bv 64%N) (bv_zero_extend 64 len).
Theorem poke_8bit'vc (left1 : bv 32%N) (flag : bool) (byte : bv 8%N) (fact0 : bv_unsigned left1 < 8%Z) : (let o1 : bv 8%N := bv_zero_extend 8 left1 in (bv_unsigned o1 ≤ 7%Z ∨ bv_ule o1 (7%bv : bv 8%N)) ∧ (let o2 : bv 8%N := bv_sub (7%bv : bv 8%N) o1 in bv_unsigned o2 = 7%Z - bv_unsigned o1 -> (let mask : bv 8%N := bv_shiftl (1%bv : bv 8%N) o2 in (match flag with | true => True | false => True end) ∧ (∀(result : bv 8%N), (match flag with | true => result = bv_or byte mask | false => result = bv_and byte (bv_not mask) end) -> (∀(i : bv 32%N), bv_ult i (8%bv : bv 32%N) -> ¬ i = bv_sub (7%bv : bv 32%N) left1 -> Z.testbit (bv_unsigned result) (bv_unsigned (bv_zero_extend 8 i)) = Z.testbit (bv_unsigned byte) (bv_unsigned (bv_zero_extend 8 i))) ∧ Z.testbit (bv_unsigned result) (bv_unsigned (bv_sub (7%bv : bv 8%N) (bv_zero_extend 8 left1))) = flag)))) ∧ (∀(result : bv 8%N), (∀(i : bv 32%N), bv_ult i (8%bv : bv 32%N) -> ¬ i = bv_sub (7%bv : bv 32%N) left1 -> Z.testbit (bv_unsigned result) (bv_unsigned (bv_zero_extend 8 i)) = Z.testbit (bv_unsigned byte) (bv_unsigned (bv_zero_extend 8 i))) ∧ Z.testbit (bv_unsigned result) (bv_unsigned (bv_sub (7%bv : bv 8%N) (bv_zero_extend 8 left1))) = flag -> (∀(i : Z), 0%Z ≤ i ∧ i < 8%Z -> ¬ i = 7%Z - bv_unsigned left1 -> Z.testbit (bv_unsigned result) i = Z.testbit (bv_unsigned byte) i) ∧ Z.testbit (bv_unsigned result) (7%Z - bv_unsigned left1) = flag).
Admitted.
