/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.Algebra.Order.Pi

/-!
# Lower Lebesgue integral for `ℝ≥0∞`-valued functions

We define the lower Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.
-/

@[expose] public section

assert_not_exists Module.Basis Norm MeasureTheory.MeasurePreserving MeasureTheory.Measure.dirac

open Set hiding restrict restrict_apply

open Filter ENNReal Topology NNReal

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ : Type*}

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
noncomputable irreducible_def lintegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => lintegral volume f) => r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => lintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => lintegral (Measure.restrict volume s) f) => r

theorem SimpleFunc.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ = f.lintegral μ := by sorry
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν := by sorry
theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg

theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)

theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    ⨆ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by sorry
theorem lintegral_mono_set {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ⊆ t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)

theorem lintegral_mono_set' {_ : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ≤ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)

theorem monotone_lintegral {_ : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono

@[simp]
theorem lintegral_const (c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ univ := by sorry
theorem lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0 := by simp

theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero

theorem lintegral_one : ∫⁻ _, (1 : ℝ≥0∞) ∂μ = μ univ := by rw [lintegral_const, one_mul]

theorem setLIntegral_const (s : Set α) (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by sorry
theorem setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ = μ s := by rw [setLIntegral_const, one_mul]

lemma iInf_mul_le_lintegral (f : α → ℝ≥0∞) : (⨅ x, f x) * μ .univ ≤ ∫⁻ x, f x ∂μ := by sorry
lemma lintegral_le_iSup_mul (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ (⨆ x, f x) * μ .univ := by sorry
variable (μ) in
/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
theorem exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by sorry
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, f a ∂μ =
      ⨆ (φ : α →ₛ ℝ≥0) (_ : ∀ x, ↑(φ x) ≤ f x), (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ := by sorry
theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : α →ₛ ℝ≥0,
      (∀ x, ↑(φ x) ≤ f x) ∧
        ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) → (map (↑) (ψ - φ)).lintegral μ < ε := by sorry
theorem iSup_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by sorry
theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by sorry
theorem le_iInf_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by sorry
theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by sorry
theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by sorry
theorem setLIntegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict s))
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ := by sorry
theorem setLIntegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hg : Measurable g)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae hg.aemeasurable (ae_of_all _ hfg)

theorem setLIntegral_mono_ae' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff' hs).2 hfg

theorem setLIntegral_mono' {s : Set α} {f g : α → ℝ≥0∞} (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae' hs (ae_of_all _ hfg)

theorem setLIntegral_le_lintegral (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x, f x ∂μ :=
  lintegral_mono' Measure.restrict_le_self le_rfl

lemma iInf_mul_le_setLIntegral (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (⨅ x ∈ s, f x) * μ s ≤ ∫⁻ x in s, f x ∂μ := by sorry
lemma setLIntegral_le_iSup_mul (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, f x ∂μ ≤ (⨆ x ∈ s, f x) * μ s := by sorry
theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)

theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by sorry
theorem setLIntegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by rw [Measure.restrict_congr_set h]

theorem setLIntegral_congr_fun_ae {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by sorry
theorem setLIntegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : EqOn f g s) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
  setLIntegral_congr_fun_ae hs <| Eventually.of_forall hfg

lemma setLIntegral_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (h's : EqOn f 0 s) :
    ∫⁻ x in s, f x ∂μ = 0 := by sorry
theorem lintegral_eq_zero_of_ae_eq_zero {f : α → ℝ≥0∞} (h : f =ᵐ[μ] 0) :
    ∫⁻ a, f a ∂μ = 0 :=
  (lintegral_congr_ae h).trans lintegral_zero

/-- The Lebesgue integral is zero iff the function is a.e. zero.

The measurability assumption is necessary, otherwise there are counterexamples: for instance, the
conclusion fails if `f` is the characteristic function of a Vitali set. -/
@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 := by sorry
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.aemeasurable

/-- The measurability assumption is necessary, otherwise there are counterexamples: for instance,
the conclusion fails if `s = univ` and `f` is the characteristic function of a Vitali set. -/
theorem setLIntegral_eq_zero_iff' {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s)) :
    ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  (lintegral_eq_zero_iff' hf).trans (ae_restrict_iff' hs)

theorem setLIntegral_eq_zero_iff {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ a in s, f a ∂μ = 0 ↔ ∀ᵐ x ∂μ, x ∈ s → f x = 0 :=
  setLIntegral_eq_zero_iff' hs hf.aemeasurable

theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by sorry
theorem setLIntegral_pos_iff {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} :
    0 < ∫⁻ a in s, f a ∂μ ↔ 0 < μ (Function.support f ∩ s) := by sorry
end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_setLIntegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε := by sorry
theorem tendsto_setLIntegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) {l : Filter ι}
    {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) := by sorry
theorem lintegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂c • μ = c • ∫⁻ a, f a ∂μ := by sorry
lemma setLIntegral_smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂(c • μ) = c • ∫⁻ a in s, f a ∂μ := by sorry
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(0 : Measure α) = 0 := by sorry
theorem lintegral_add_measure (f : α → ℝ≥0∞) (μ ν : Measure α) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by sorry
theorem lintegral_finset_sum_measure {ι} (s : Finset ι) (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫⁻ a, f a ∂μ i :=
  let F : Measure α →+ ℝ≥0∞ :=
    { toFun := (lintegral · f),
      map_zero' := lintegral_zero_measure f,
      map_add' := lintegral_add_measure f }
  map_sum F μ s

@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    ∫⁻ a, f a ∂Measure.sum μ = ∑' i, ∫⁻ a, f a ∂μ i := by sorry
theorem hasSum_lintegral_measure {ι} {_ : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.hasSum

@[simp]
theorem lintegral_of_isEmpty {α} [MeasurableSpace α] [IsEmpty α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = 0 := by sorry
theorem setLIntegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 := by sorry
theorem setLIntegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by sorry
theorem setLIntegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    ∫⁻ x in s, f x ∂μ = 0 := by sorry
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    ∫⁻ a, g (f a) ∂μ = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by dsimp only; rw [h]

-- TODO: Need a better way of rewriting inside of an integral
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : ∫⁻ a, g (f₁ a) (f₂ a) ∂μ = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by dsimp only; rw [h₁, h₂]

theorem lintegral_indicator_le (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a, s.indicator f a ∂μ ≤ ∫⁻ a in s, f a ∂μ := by sorry
theorem lintegral_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by sorry
lemma setLIntegral_indicator {s t : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by sorry
theorem lintegral_indicator₀ {s : Set α} (hs : NullMeasurableSet s μ) (f : α → ℝ≥0∞) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ := by sorry
lemma setLIntegral_indicator₀ (f : α → ℝ≥0∞) {s t : Set α}
    (hs : NullMeasurableSet s (μ.restrict t)) :
    ∫⁻ a in t, s.indicator f a ∂μ = ∫⁻ a in s ∩ t, f a ∂μ := by sorry
theorem lintegral_indicator_const_le (s : Set α) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ ≤ c * μ s :=
  (lintegral_indicator_le _ _).trans (setLIntegral_const s c).le

theorem lintegral_indicator_const₀ {s : Set α} (hs : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s := by sorry
theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const₀ hs.nullMeasurableSet c

lemma setLIntegral_eq_of_support_subset {s : Set α} {f : α → ℝ≥0∞} (hsf : f.support ⊆ s) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂μ := by sorry
theorem setLIntegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    ∫⁻ x in { x | f x = r }, f x ∂μ = r * μ { x | f x = r } := by sorry
theorem lintegral_indicator_one_le (s : Set α) : ∫⁻ a, s.indicator 1 a ∂μ ≤ μ s :=
  (lintegral_indicator_const_le _ _).trans <| (one_mul _).le

@[simp]
theorem lintegral_indicator_one₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s :=
  (lintegral_indicator_const₀ hs _).trans <| one_mul _

theorem lintegral_indicator_one {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator 1 a ∂μ = μ s := by sorry
theorem Measure.ext_iff_lintegral (ν : Measure α) :
    μ = ν ↔ ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν := by sorry
theorem Measure.ext_of_lintegral (ν : Measure α)
    (hμν : ∀ f : α → ℝ≥0∞, Measurable f → ∫⁻ a, f a ∂μ = ∫⁻ a, f a ∂ν) : μ = ν :=
  (μ.ext_iff_lintegral ν).mpr hμν

open Measure

open scoped Function -- required for scoped `on` notation

theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ := by sorry
theorem lintegral_iUnion [Countable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) hd.aedisjoint f

theorem lintegral_biUnion₀ {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ := by sorry
theorem lintegral_biUnion {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).nullMeasurableSet) hd.aedisjoint f

theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ b ∈ s, NullMeasurableSet (t b) μ)
    (f : α → ℝ≥0∞) : ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ := by sorry
theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) f

theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ := by sorry
theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ := by sorry
theorem lintegral_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∫⁻ a in s ∪ t, f a ∂μ ≤ ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ := by sorry
theorem lintegral_inter_add_diff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ := by sorry
theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ := by sorry
lemma lintegral_piecewise (hs : MeasurableSet s) (f g : α → ℝ≥0∞) [∀ j, Decidable (j ∈ s)] :
    ∫⁻ a, s.piecewise f g a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, g a ∂μ := by sorry
theorem setLIntegral_compl {f : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hfs : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∫⁻ x in sᶜ, f x ∂μ = ∫⁻ x, f x ∂μ - ∫⁻ x in s, f x ∂μ := by sorry
theorem setLIntegral_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α → ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    ∫⁻ x in ⋃ i, s i, f x ∂μ = ⨆ i, ∫⁻ x in s i, f x ∂μ := by sorry
theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, max (f x) (g x) ∂μ =
      ∫⁻ x in { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in { x | g x < f x }, f x ∂μ := by sorry
theorem setLIntegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    ∫⁻ x in s, max (f x) (g x) ∂μ =
      ∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ := by sorry
theorem setLIntegral_lt_top_of_le_nnreal {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0∞}
    (hbdd : ∃ y : ℝ≥0, ∀ x ∈ s, f x ≤ y) : ∫⁻ x in s, f x ∂μ < ∞ := by sorry
theorem setLIntegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hbdd : BddAbove (f '' s)) : ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_le_nnreal hs <| hbdd.imp fun _M hM _x hx ↦
    ENNReal.coe_le_coe.2 <| hM (mem_image_of_mem f hx)

theorem setLIntegral_lt_top_of_isCompact [TopologicalSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    ∫⁻ x in s, f x ∂μ < ∞ :=
  setLIntegral_lt_top_of_bddAbove hs (hsc.image hf).bddAbove

end MeasureTheory
