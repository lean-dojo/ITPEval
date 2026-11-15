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
Theorem peekthenpoke'vc (addr : list (bv 8%N)) (len : bv 32%N) (start : bv 32%N) (fact0 : 8%Z * Z.of_nat (length addr) < 4294967296%Z) (fact1 : 0%Z ≤ bv_unsigned len) (fact2 : bv_unsigned len < 64%Z) (fact3 : bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr)) : bv_unsigned len ≤ 64%Z ∧ bv_unsigned start + bv_unsigned len < 4294967296%Z ∧ 8%Z * Z.of_nat (length addr) < 4294967296%Z ∧ (∀(value : bv 64%N), (8%Z * Z.of_nat (length addr) < bv_unsigned start + bv_unsigned len -> value = (0%bv : bv 64%N)) ∧ (bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr) -> (∀(i : Z), 0%Z ≤ i ∧ i < bv_unsigned len -> Z.testbit (bv_unsigned value) i = nth8_stream addr (bv_unsigned start + bv_unsigned len - i - 1%Z)) ∧ (∀(i : Z), bv_unsigned len ≤ i ∧ i < 64%Z -> Z.testbit (bv_unsigned value) i = false)) -> (bv_unsigned len < 64%Z ∧ bv_unsigned start + bv_unsigned len < 4294967296%Z ∧ 8%Z * Z.of_nat (length addr) < 4294967296%Z) ∧ (∀(addr1 : list (bv 8%N)), length addr1 = length addr -> (∀(res : Z), (- 2%Z ≤ res ∧ res ≤ 0%Z) ∧ (res = - 1%Z) = (8%Z * Z.of_nat (length addr1) < bv_unsigned start + bv_unsigned len) ∧ (res = - 2%Z) = (bv_unsigned (maxvalue len) ≤ bv_unsigned value ∧ bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr1)) ∧ (res = 0%Z) = (bv_unsigned value < bv_unsigned (maxvalue len) ∧ bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr1)) ∧ (res = 0%Z -> (∀(i : Z), 0%Z ≤ i ∧ i < bv_unsigned start -> nth8_stream addr i = nth8_stream addr1 i) ∧ (∀(i : Z), bv_unsigned start ≤ i ∧ i < bv_unsigned start + bv_unsigned len -> nth8_stream addr1 i = Z.testbit (bv_unsigned value) (bv_unsigned len - i - 1%Z + bv_unsigned start)) ∧ (∀(i : Z), bv_unsigned start + bv_unsigned len ≤ i ∧ i < 8%Z * Z.of_nat (length addr1) -> nth8_stream addr1 i = nth8_stream addr i)) -> res = 0%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 8%Z * Z.of_nat (length addr1) -> nth8_stream addr1 i = nth8_stream addr i)))).
Admitted.
