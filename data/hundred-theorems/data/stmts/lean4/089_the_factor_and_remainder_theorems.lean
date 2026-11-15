/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.Nat.Lattice

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R]

theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with := by sorry
variable {p q : R[X]}

theorem finiteMultiplicity_of_degree_pos_of_monic (hp : (0 : WithBot ℕ) < degree p) (hmp : Monic p)
    (hq : q ≠ 0) : FiniteMultiplicity p q :=
  have zn0 : (0 : R) ≠ 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p ≠ 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r ≠ 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) ≠ 0 := hpn1.symm ▸ zn0.symm
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r ≠ 0 := by sorry
lemma eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = p * C q.leadingCoeff := by sorry
lemma eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by sorry
end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p :=
  have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt
    (by
      rw [hq.degree_mul_comm, hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])

/-- See `divByMonic`. -/
noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

/-- `divByMonic`, denoted as `p /ₘ q`, gives the quotient of `p` by a monic polynomial `q`. -/
def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

/-- `modByMonic`, denoted as `p  %ₘ q`, gives the remainder of `p` by a monic polynomial `q`. -/
def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q := by sorry
theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q ≠ 1) :
    natDegree (p %ₘ q) < q.natDegree := by sorry
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by sorry
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by sorry
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]

@[simp]
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]

theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  dif_neg hq

theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  dif_neg hq

theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) ≤ degree q := by sorry
theorem degree_modByMonic_le_left : degree (p %ₘ q) ≤ degree p := by sorry
theorem natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Monic) :
    natDegree (p %ₘ g) ≤ g.natDegree :=
  natDegree_le_natDegree (degree_modByMonic_le p hg)

theorem natDegree_modByMonic_le_left : natDegree (p %ₘ q) ≤ natDegree p :=
  natDegree_le_natDegree degree_modByMonic_le_left

theorem X_dvd_sub_C : X ∣ p - C (p.coeff 0) := by sorry
theorem modByMonic_eq_sub_mul_div :
    ∀ p q : R[X], p %ₘ q = p - q * (p /ₘ q) := by sorry
theorem modByMonic_add_div (p q : R[X]) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p q)

theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := modByMonic_add_div p q
    rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩

theorem degree_add_divByMonic (hq : Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by sorry
theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q ≤ degree p then by
        haveI := Nontrivial.of_polynomial_ne hp0
        rw [← degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
          degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold divByMonic divModByMonicAux
        simp [dif_pos hq, h, degree_zero, bot_le]
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le

theorem degree_divByMonic_lt (p q : R[X]) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      haveI := Nontrivial.of_polynomial_ne hp0
      rw [(divByMonic_eq_zero_iff hq).2 hpq, degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      haveI := Nontrivial.of_polynomial_ne hp0
      rw [← degree_add_divByMonic hq (not_lt.1 hpq), degree_eq_natDegree hq.ne_zero,
        degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 hpq)]
      exact
        Nat.cast_lt.2
          (Nat.lt_add_of_pos_left (Nat.cast_lt.1 <|
            by simpa [degree_eq_natDegree hq.ne_zero] using h0q))
  else by
    rwa [divByMonic_eq_of_not_monic _ hq, degree_zero, bot_lt_iff_ne_bot, degree_ne_bot]

theorem natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by sorry
theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by sorry
theorem map_mod_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by sorry
theorem map_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_divByMonic f hq).1

theorem map_modByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2

theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p q, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div, mul_sub, ← hr]
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    have hrpq0 : leadingCoeff (r - p /ₘ q) ≠ 0 := fun h =>
      hpq0 <|
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) ≠ 0 := by rwa [Monic.def.1 hq, one_mul]
    rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.coe_lt_coe.1 this)⟩


/-- See `Polynomial.mul_self_modByMonic` for the other multiplication order. That version, unlike
this one, requires commutativity. -/
@[simp]
lemma self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by sorry
theorem map_dvd_map [Ring S] (f : R →+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by sorry
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  (modByMonic_eq_zero_iff_dvd (by convert monic_one (R := R))).2 (one_dvd _)

@[simp]
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by sorry
theorem sum_modByMonic_coeff (hq : q.Monic) {n : ℕ} (hn : q.degree ≤ n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by sorry
theorem mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by sorry
lemma coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1) := by sorry
theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = ∑ i ∈ Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by sorry
variable (R) in
theorem not_isField : ¬IsField R[X] := by sorry
section multiplicity

/-- An algorithm for deciding polynomial divisibility.
Prefer `Classical.dec`, as the algorithm relies on `%ₘ` and so is `noncomputable`.
-/
@[deprecated Classical.dec (since := "2026-02-07")]
def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p ≠ 0) : FiniteMultiplicity (X - C a) p := by sorry
def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := Classical.decPred _
    Nat.find (finiteMultiplicity_X_sub_C a h0)

theorem rootMultiplicity_eq_natFind_of_ne_zero {p : R[X]} (p0 : p ≠ 0) {a : R}
    [DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p] :
    rootMultiplicity a p = Nat.find (finiteMultiplicity_X_sub_C a p0) := by sorry
theorem rootMultiplicity_eq_multiplicity [DecidableEq R]
    (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if p = 0 then 0 else multiplicity (X - C a) p := by sorry
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  dif_pos rfl

@[simp]
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by sorry
theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    classical
    rw [rootMultiplicity_eq_multiplicity, if_neg h]; apply pow_multiplicity_dvd

theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p := by sorry
theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q := by sorry
end multiplicity

end Ring

section CommRing

variable [CommRing R] {p p₁ p₂ q : R[X]}

@[simp]
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by sorry
theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs => rw [← modByMonic_add_div p, modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm

theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by sorry
theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by sorry
theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]}
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by sorry
theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by sorry
lemma IsRoot.dvd_coeff_zero {p : R[X]} {x : R} (h : p.IsRoot x) : x ∣ p.coeff 0 := by sorry
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by sorry
theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

@[simp]
theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x := by sorry
theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  rootMultiplicity_pos'.trans (and_iff_right hp)

theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0 := by sorry
lemma mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by sorry
lemma modByMonic_eq_of_dvd_sub (hq : q.Monic) (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by sorry
lemma add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by sorry
lemma neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p %ₘ q) := by sorry
lemma sub_modByMonic (p₁ p₂ q : R[X]) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q := by sorry
lemma mul_modByMonic (p₁ p₂ q : R[X]) : (p₁ * p₂) %ₘ q = (p₁ %ₘ q) * (p₂ %ₘ q) %ₘ q := by sorry
lemma eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t = (p.comp (X + C t)).trailingCoeff := by sorry
lemma le_rootMultiplicity_iff (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p := by sorry
lemma rootMultiplicity_le_iff (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - C a) ^ (n + 1) ∣ p := by sorry
lemma rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by sorry
lemma le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q ≠ 0) :
    rootMultiplicity x p + rootMultiplicity x q ≤ rootMultiplicity x (p * q) := by sorry
lemma rootMultiplicity_le_rootMultiplicity_of_dvd {p q : R[X]} (hq : q ≠ 0) (hpq : p ∣ q) (x : R) :
    p.rootMultiplicity x ≤ q.rootMultiplicity x := by sorry
lemma pow_rootMultiplicity_not_dvd (p0 : p ≠ 0) (a : R) :
    ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← rootMultiplicity_le_iff p0]

/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree` for the general case. -/
lemma rootMultiplicity_eq_natTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree := by sorry
lemma leadingCoeff_divByMonic_of_monic (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by sorry
variable [IsDomain R]

lemma degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_isRoot.2 hx
  have : IsUnit (X - C x) ∨ IsUnit g := hi.isUnit_or_isUnit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - C x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - C x) = 0 := degree_eq_zero_of_isUnit h
      rw [h₁] at h₂; exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_isUnit hgu, add_zero]

lemma _root_.Irreducible.not_isRoot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) {x : R} : ¬p.IsRoot x :=
  fun hr ↦ hdeg <| natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hi hr

lemma _root_.Irreducible.isRoot_eq_bot_of_natDegree_ne_one
    (hi : Irreducible p) (hdeg : p.natDegree ≠ 1) : p.IsRoot = ⊥ :=
  le_bot_iff.mp fun _ ↦ hi.not_isRoot_of_natDegree_ne_one hdeg

lemma _root_.Irreducible.subsingleton_isRoot [IsLeftCancelMulZero R]
    (hi : Irreducible p) : { x | p.IsRoot x }.Subsingleton :=
  fun _ hx ↦ (subsingleton_isRoot_of_natDegree_eq_one <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hi hx) hx

lemma leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - C a)) = leadingCoeff p := by sorry
lemma eq_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : p.leadingCoeff = q.leadingCoeff) :
    p = q := by sorry
lemma associated_of_dvd_of_natDegree_le_of_leadingCoeff {p q : R[X]} (hpq : p ∣ q)
    (h₁ : q.natDegree ≤ p.natDegree) (h₂ : q.leadingCoeff ∣ p.leadingCoeff) :
    Associated p q :=
  have ⟨r, hr⟩ := hpq
  have ⟨u, hu⟩ := associated_of_dvd_dvd ⟨leadingCoeff r, hr ▸ leadingCoeff_mul p r⟩ h₂
  ⟨Units.map C.toMonoidHom u, eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (by rwa [Units.mul_right_dvd]) (by simpa [natDegree_mul_C] using h₁) (by simpa using hu)⟩

lemma associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q ≠ 0)
    (h₁ : q.natDegree ≤ p.natDegree) : Associated p q :=
  associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

lemma associated_of_dvd_of_degree_eq {K} [Field K] {p q : K[X]} (hpq : p ∣ q)
    (h₁ : p.degree = q.degree) : Associated p q :=
  (Classical.em (q = 0)).elim (fun hq ↦ (show p = q by simpa [hq] using h₁) ▸ Associated.refl p)
    (associated_of_dvd_of_natDegree_le hpq · (natDegree_le_natDegree h₁.ge))

lemma eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le {R} [CommSemiring R] {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = C q.leadingCoeff * p := by sorry
end CommRing

end Polynomial
