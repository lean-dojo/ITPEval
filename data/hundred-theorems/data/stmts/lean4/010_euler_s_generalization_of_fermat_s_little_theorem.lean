/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralDomain

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `RingTheory.IntegralDomain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`Fintype.fieldOfDomain`).

## Main results

1. `Fintype.card_units`: The unit group of a finite field has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
  - `q-1` if `q-1 ∣ i`
  - `0`   otherwise
3. `FiniteField.card`: The cardinality `q` is a power of the characteristic of `K`.
  See `FiniteField.card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `Fintype Kˣ` can be inferred from `Fintype K` in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.

-/

@[expose] public section


variable {K : Type*} {R : Type*}

local notation "q" => Fintype.card K

open Finset

open scoped Polynomial

namespace FiniteField

section Polynomial

variable [CommRing R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * #(univ.image fun x => eval x p) :=
  Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ ≤ Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
  letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push Not at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_cancel]⟩
  fun hd : Disjoint _ _ =>
  lt_irrefl (2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))) <|
    calc 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))
        ≤ 2 * Fintype.card R := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
      _ = Fintype.card R + Fintype.card R := two_mul _
      _ < natDegree f * #(univ.image fun x : R => eval x f) +
            natDegree (-g) * #(univ.image fun x : R => eval x (-g)) :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)) := by sorry
end Polynomial

theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by sorry
theorem card_cast_subgroup_card_ne_zero [Ring K] [NoZeroDivisors K] [Nontrivial K]
    (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) ≠ 0 := by sorry
theorem sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] (hg : G ≠ ⊥) :
    ∑ x : G, (x.val : K) = 0 := by sorry
theorem sum_subgroup_units [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0 := by sorry
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := by sorry
variable [GroupWithZero K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 := by sorry
theorem pow_card (a : K) : a ^ q = a := by sorry
theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by sorry
end

variable (K) [Field K] [Fintype K]

/-- The cardinality `q` is a power of the characteristic of `K`. -/
@[stacks 09HY "first part"]
theorem card (p : ℕ) [CharP K p] : ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by sorry
theorem card' : ∃ (p : ℕ), CharP K p ∧ ∃ (n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩

lemma isPrimePow_card : IsPrimePow (Fintype.card K) := by sorry
theorem cast_card_eq_zero : (q : K) = 0 := by sorry
theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by sorry
theorem sum_pow_units [DecidableEq K] (i : ℕ) :
    (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by sorry
theorem sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by sorry
section frobenius

variable (R) [CommRing R] [Algebra K R]

/-- If `R` is an algebra over a finite field `K`, the Frobenius `K`-algebra endomorphism of `R` is
  given by raising every element of `R` to its `#K`-th power. -/
@[simps!] def frobeniusAlgHom : R →ₐ[K] R where
  __ := powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by sorry
theorem coe_frobeniusAlgHom : ⇑(frobeniusAlgHom K R) = (· ^ q) := rfl

/-- If `R` is a perfect ring and an algebra over a finite field `K`, the Frobenius `K`-algebra
  endomorphism of `R` is an automorphism. -/
@[simps!] noncomputable def frobeniusAlgEquiv (p : ℕ) [ExpChar R p] [PerfectRing R p] : R ≃ₐ[K] R :=
  .ofBijective (frobeniusAlgHom K R) <| by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom, card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
    apply bijective_iterateFrobenius

variable (L : Type*) [Field L] [Algebra K L]

/-- If `L/K` is an algebraic extension of a finite field, the Frobenius `K`-algebra endomorphism
  of `L` is an automorphism. -/
@[simps!] noncomputable def frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : Gal(L/K) :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)

theorem coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] :
    ⇑(frobeniusAlgEquivOfAlgebraic K L) = (· ^ q) := rfl

lemma coe_frobeniusAlgEquivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : ℕ) :
    (⇑(frobeniusAlgEquivOfAlgebraic K L))^[n] = (· ^ (Fintype.card K ^ n)) :=
  pow_iterate (Fintype.card K) n

variable [Finite L]

open Polynomial in
theorem orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K L :=
  (orderOf_eq_iff Module.finrank_pos).mpr <| by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x ↦ ?_, fun m lt pos eq ↦ ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_subset_roots (R := L) (p := X ^ q ^ m - X) (Z := univ) fun x _ ↦ by
      simp_rw [mem_roots', IsRoot, eval_sub, eval_pow, eval_X]
      have := DFunLike.congr_fun eq x
      rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply, ← sub_eq_zero] at this
      refine ⟨fun h ↦ ?_, this⟩
      simpa [if_neg (Nat.one_lt_pow pos.ne' Fintype.one_lt_card).ne] using congr_arg (coeff · 1) h
    refine this.not_gt (((natDegree_sub_le ..).trans_eq ?_).trans_lt <|
      (Nat.pow_lt_pow_right Fintype.one_lt_card lt).trans_eq Module.card_eq_pow_finrank.symm)
    simp [Nat.one_le_pow _ _ Fintype.card_pos]

theorem orderOf_frobeniusAlgEquivOfAlgebraic :
    orderOf (frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L := by sorry
theorem bijective_frobeniusAlgHom_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgHom K L ^ n.1 :=
  let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans <|
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)

theorem bijective_frobeniusAlgEquivOfAlgebraic_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgEquivOfAlgebraic K L ^ n.1 :=
  ((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp <| by
    simpa only [Function.comp_def, map_pow] using bijective_frobeniusAlgHom_pow K L

instance (K L) [Finite L] [Field K] [Field L] [Algebra K L] : IsCyclic Gal(L/K) where
  exists_zpow_surjective :=
    have := Finite.of_injective _ (algebraMap K L).injective
    have := Fintype.ofFinite K
    ⟨frobeniusAlgEquivOfAlgebraic K L,
      fun f ↦ have ⟨n, hn⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f; ⟨n, hn⟩⟩

open Polynomial in
theorem minpoly_frobeniusAlgHom :
    minpoly K (frobeniusAlgHom K L).toLinearMap = X ^ Module.finrank K L - 1 :=
  minpoly.eq_of_linearIndependent _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x ↦ by simpa [sub_eq_zero, Module.End.coe_pow, orderOf_frobeniusAlgHom] using
      congr($(pow_orderOf_eq_one (frobeniusAlgHom K L)) x)) _
    (degree_X_pow_sub_C Module.finrank_pos _) <| by
      simpa [← AlgHom.toEnd_apply, ← map_pow] using (linearIndependent_algHom_toLinearMap K L L := by sorry
end frobenius

open Polynomial

section

variable [Fintype K] (K' : Type*) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by sorry
theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_natDegree_eq K' <| Nat.one_lt_pow hn hp

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt <|
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' <| Nat.one_lt_pow hn hp

end

theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by sorry
variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by sorry
open Polynomial

theorem expand_card (f : K[X]) : expand K q f = f ^ q := by sorry
end FiniteField

namespace ZMod

open FiniteField Polynomial

set_option backward.isDefEq.respectTransparency false in
theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x := by sorry
end ZMod

/-- If `p` is a prime natural number and `x` is an integer number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [ZMOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
theorem Nat.sq_add_sq_zmodEq (p : ℕ) [Fact p.Prime] (x : ℤ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ≡ x [ZMOD p] := by sorry
theorem Nat.sq_add_sq_modEq (p : ℕ) [Fact p.Prime] (x : ℕ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p] := by sorry
namespace CharP

theorem sq_add_sq (R : Type*) [Ring R] [IsDomain R] (p : ℕ) [NeZero p] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x := by sorry
end CharP

open scoped Nat

open ZMod

/-- The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem ZMod.pow_totient {n : ℕ} (x : (ZMod n)ˣ) : x ^ φ n = 1 := by sorry
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by sorry
instance instFiniteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
| 0 => Finite.of_fintype ℤˣ
| _ + 1 => inferInstance

open FiniteField

namespace ZMod

variable {p : ℕ} [Fact p.Prime]

instance : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_bot_eq_top <| top_unique (a := ⊥) fun n _ ↦
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this

theorem fieldRange_castHom_eq_bot (p : ℕ) [Fact p.Prime] [DivisionRing K] [CharP K p] :
    (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K) := by sorry
theorem pow_card (x : ZMod p) : x ^ p = x := by sorry
theorem pow_card_pow {n : ℕ} (x : ZMod p) : x ^ p ^ n = x := by sorry
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by sorry
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by sorry
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by sorry
theorem pow_card_sub_one_eq_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by sorry
lemma pow_card_sub_one (a : ZMod p) :
    a ^ (p - 1) = if a ≠ 0 then 1 else 0 := by sorry
theorem orderOf_units_dvd_card_sub_one (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| units_pow_card_sub_one_eq_one _ _

theorem orderOf_dvd_card_sub_one {a : ZMod p} (ha : a ≠ 0) :
    orderOf a ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| pow_card_sub_one_eq_one ha

open Polynomial

theorem expand_card (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

end ZMod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem Int.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by sorry
theorem Int.prime_dvd_pow_sub_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    (p : ℤ) ∣ n ^ (p - 1) - 1 :=
  (ModEq.pow_card_sub_one_eq_one hp hpn).symm.dvd

theorem Int.ModEq.pow_prime_eq_self {p : ℕ} (hp : Nat.Prime p) (n : ℤ) : n ^ p ≡ n [ZMOD p] := by sorry
theorem Int.prime_dvd_pow_self_sub {p : ℕ} (hp : Nat.Prime p) (n : ℤ) : (p : ℤ) ∣ n ^ p - n :=
  (ModEq.pow_prime_eq_self hp n).symm.dvd

theorem Int.ModEq.pow_eq_pow {p x y : ℕ} (hp : Nat.Prime p) (h : p - 1 ∣ x - y) (hxy : y ≤ x)
    (hy : 0 < y) (n : ℤ) : n ^ x ≡ n ^ y [ZMOD p] := by sorry
theorem Nat.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] := by sorry
theorem Nat.pow_card_sub_one_sub_one_mod_card {p : ℕ} (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    (n ^ (p - 1) - 1) % p = 0 :=
  Nat.sub_mod_eq_zero_of_mod_eq (Nat.ModEq.pow_card_sub_one_eq_one hp hpn)

theorem pow_pow_modEq_one (p m a : ℕ) : (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m] := by sorry
theorem ZMod.eq_one_or_isUnit_sub_one {n p k : ℕ} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n)
    (ha : (orderOf a).Coprime n) : a = 1 ∨ IsUnit (a - 1) := by sorry
section prime_subfield

variable {F : Type*} [Field F]

theorem mem_bot_iff_intCast (p : ℕ) [Fact p.Prime] (K) [DivisionRing K] [CharP K p] {x : K} :
    x ∈ (⊥ : Subfield K) ↔ ∃ n : ℤ, n = x := by sorry
variable (F) (p : ℕ) [Fact p.Prime] [CharP F p]

theorem Subfield.card_bot : Nat.card (⊥ : Subfield F) = p := by sorry
def Subfield.fintypeBot : Fintype (⊥ : Subfield F) :=
  Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ ↦ by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

open Polynomial

theorem Subfield.roots_X_pow_char_sub_X_bot :
    letI := Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by sorry
theorem Subfield.splits_bot :
    Splits (X ^ p - X : (⊥ : Subfield F)[X]) := by sorry
theorem Subfield.mem_bot_iff_pow_eq_self {x : F} : x ∈ (⊥ : Subfield F) ↔ x ^ p = x := by sorry
end prime_subfield

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  have : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by sorry
end Finite

variable [Fintype F]

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by sorry
theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by sorry
theorem unit_isSquare_iff (hF : ringChar F ≠ 2) (a : Fˣ) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by sorry
theorem isSquare_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by sorry
end FiniteField
