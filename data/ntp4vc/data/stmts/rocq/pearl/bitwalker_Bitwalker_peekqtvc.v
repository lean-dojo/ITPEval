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
Theorem peek'vc (len : bv 32%N) (start : bv 32%N) (addr : list (bv 8%N)) (fact0 : bv_unsigned len ≤ 64%Z) (fact1 : bv_unsigned start + bv_unsigned len < 4294967296%Z) (fact2 : 8%Z * Z.of_nat (length addr) < 4294967296%Z) : (bv_unsigned start + bv_unsigned len < 4294967296%Z ∨ bv_ule (bv_add (bv_zero_extend 128 start) (bv_zero_extend 128 len)) (bv_zero_extend 128 (4294967295%bv : bv 32%N))) ∧ (bv_unsigned (bv_add start len) = bv_unsigned start + bv_unsigned len -> (if decide (8%Z * Z.of_nat (length addr) < bv_unsigned (bv_add start len)) then bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr) -> (∀(i : Z), 0%Z ≤ i ∧ i < bv_unsigned len -> Z.testbit (bv_unsigned (0%bv : bv 64%N)) i = nth8_stream addr (bv_unsigned start + bv_unsigned len - i - 1%Z)) ∧ (∀(i : Z), bv_unsigned len ≤ i ∧ i < 64%Z -> Z.testbit (bv_unsigned (0%bv : bv 64%N)) i = false) else (bv_unsigned len ≤ 64%Z ∨ bv_ule len (64%bv : bv 32%N)) ∧ (let lstart : bv 32%N := bv_sub (64%bv : bv 32%N) len in bv_unsigned lstart = 64%Z - bv_unsigned len -> ((0%Z ≤ 0%Z ∧ 0%Z ≤ bv_unsigned len) ∧ (∀(j : Z), bv_unsigned len - 0%Z ≤ j ∧ j < bv_unsigned len -> Z.testbit (bv_unsigned (0%bv : bv 64%N)) j = nth8_stream addr (bv_unsigned start + bv_unsigned len - j - 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < bv_unsigned len - 0%Z -> Z.testbit (bv_unsigned (0%bv : bv 64%N)) j = false) ∧ (∀(j : Z), bv_unsigned len ≤ j ∧ j < 64%Z -> Z.testbit (bv_unsigned (0%bv : bv 64%N)) j = false)) ∧ (∀(i : bv 32%N) (retval : bv 64%N), (0%Z ≤ bv_unsigned i ∧ bv_unsigned i ≤ bv_unsigned len) ∧ (∀(j : Z), bv_unsigned len - bv_unsigned i ≤ j ∧ j < bv_unsigned len -> Z.testbit (bv_unsigned retval) j = nth8_stream addr (bv_unsigned start + bv_unsigned len - j - 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < bv_unsigned len - bv_unsigned i -> Z.testbit (bv_unsigned retval) j = false) ∧ (∀(j : Z), bv_unsigned len ≤ j ∧ j < 64%Z -> Z.testbit (bv_unsigned retval) j = false) -> (if decide (bv_ult i len) then (bv_unsigned start + bv_unsigned i < 4294967296%Z ∨ bv_ule (bv_add (bv_zero_extend 128 start) (bv_zero_extend 128 i)) (bv_zero_extend 128 (4294967295%bv : bv 32%N))) ∧ (bv_unsigned (bv_add start i) = bv_unsigned start + bv_unsigned i -> (8%Z * Z.of_nat (length addr) < 4294967296%Z ∧ bv_unsigned (bv_add start i) < 8%Z * Z.of_nat (length addr)) ∧ (bv_unsigned lstart + bv_unsigned i < 4294967296%Z ∨ bv_ule (bv_add (bv_zero_extend 128 lstart) (bv_zero_extend 128 i)) (bv_zero_extend 128 (4294967295%bv : bv 32%N))) ∧ (bv_unsigned (bv_add lstart i) = bv_unsigned lstart + bv_unsigned i -> bv_unsigned (bv_add lstart i) < 64%Z ∧ (∀(o1 : bv 64%N), (∀(i1 : Z), (0%Z ≤ i1 ∧ i1 < 64%Z) ∧ ¬ i1 = 63%Z - bv_unsigned (bv_add lstart i) -> Z.testbit (bv_unsigned o1) i1 = Z.testbit (bv_unsigned retval) i1) ∧ nth8_stream addr (bv_unsigned (bv_add start i)) = Z.testbit (bv_unsigned o1) (63%Z - bv_unsigned (bv_add lstart i)) -> (bv_unsigned i + 1%Z < 4294967296%Z ∨ bv_ule (bv_add (bv_zero_extend 128 i) (bv_zero_extend 128 (1%bv : bv 32%N))) (bv_zero_extend 128 (4294967295%bv : bv 32%N))) ∧ (bv_unsigned (bv_add i (1%bv : bv 32%N)) = bv_unsigned i + 1%Z -> (0%Z ≤ bv_unsigned len - bv_unsigned i ∧ bv_unsigned len - bv_unsigned (bv_add i (1%bv : bv 32%N)) < bv_unsigned len - bv_unsigned i) ∧ (0%Z ≤ bv_unsigned (bv_add i (1%bv : bv 32%N)) ∧ bv_unsigned (bv_add i (1%bv : bv 32%N)) ≤ bv_unsigned len) ∧ (∀(j : Z), bv_unsigned len - bv_unsigned (bv_add i (1%bv : bv 32%N)) ≤ j ∧ j < bv_unsigned len -> Z.testbit (bv_unsigned o1) j = nth8_stream addr (bv_unsigned start + bv_unsigned len - j - 1%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < bv_unsigned len - bv_unsigned (bv_add i (1%bv : bv 32%N)) -> Z.testbit (bv_unsigned o1) j = false) ∧ (∀(j : Z), bv_unsigned len ≤ j ∧ j < 64%Z -> Z.testbit (bv_unsigned o1) j = false))))) else (8%Z * Z.of_nat (length addr) < bv_unsigned start + bv_unsigned len -> retval = (0%bv : bv 64%N)) ∧ (bv_unsigned start + bv_unsigned len ≤ 8%Z * Z.of_nat (length addr) -> (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < bv_unsigned len -> Z.testbit (bv_unsigned retval) i1 = nth8_stream addr (bv_unsigned start + bv_unsigned len - i1 - 1%Z)) ∧ (∀(i1 : Z), bv_unsigned len ≤ i1 ∧ i1 < 64%Z -> Z.testbit (bv_unsigned retval) i1 = false))))))).
Admitted.
