/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Basic

/-!
# (Semi)normed groups: basic theory

We prove basic properties of (semi)normed groups.

## Tags

normed group
-/

@[expose] public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ * b‖ :=
  SeminormedGroup.dist_eq _ _

@[to_additive]
theorem dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹ * a‖ := by sorry
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by sorry
lemma dist_one_left (a : E) : dist 1 a = ‖a‖ := by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]
lemma dist_one : dist (1 : E) = norm := funext dist_one_left

@[to_additive]
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by sorry
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]
theorem norm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖ = ‖a ^ n‖ := by sorry
theorem norm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖ = ‖a ^ n‖ := by sorry
theorem norm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖ := by sorry
theorem norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖ = ‖a‖ :=
  norm_isUnit_zsmul a n.isUnit

open scoped symmDiff in
@[to_additive]
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by sorry
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by sorry
theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₃_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₄_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ ≤ ‖a / b‖ + ‖b / c‖ := by sorry
lemma norm_le_norm_div_add (a b : E) : ‖a‖ ≤ ‖a / b‖ + ‖b‖ := by sorry
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by sorry
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _

@[to_additive (attr := simp) norm_zero]
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]

@[to_additive]
theorem ne_one_of_norm_ne_zero : ‖a‖ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by sorry
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by sorry
theorem norm_div_le (a b : E) : ‖a / b‖ ≤ ‖a‖ + ‖b‖ := by sorry
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ‖a₁‖ ≤ r₁) (H₂ : ‖a₂‖ ≤ r₂) : ‖a₁ / a₂‖ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]
theorem dist_le_norm_add_norm' (a b : E) : dist a b ≤ ‖a‖ + ‖b‖ := by sorry
theorem abs_norm_sub_norm_le_norm_inv_mul (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a⁻¹ * b‖ := by sorry
theorem norm_sub_norm_le_norm_inv_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]
theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by sorry
theorem dist_norm_norm_le_norm_inv_mul (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by sorry
theorem norm_le_norm_add_norm_inv_mul (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u⁻¹ * v‖ := by sorry
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by sorry
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _

/-- An analogue of `norm_le_mul_norm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `norm_le_add_norm_add` for the addition from the left. -/]
theorem norm_le_mul_norm_add' (u v : E) : ‖v‖ ≤ ‖u * v‖ + ‖u‖ :=
  calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ ≤ ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]
lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by sorry
lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by sorry
lemma norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖ := by sorry
lemma norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖ := by sorry
theorem ball_eq_norm_inv_mul_lt (y : E) (ε : ℝ) : ball y ε = { x | ‖x⁻¹ * y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp

@[to_additive]
theorem mem_ball_iff_norm_inv_mul_lt : b ∈ ball a r ↔ ‖b⁻¹ * a‖ < r := by sorry
theorem mem_ball_iff_norm_inv_mul_lt' : b ∈ ball a r ↔ ‖a⁻¹ * b‖ < r := by sorry
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive]
theorem mem_closedBall_iff_norm_inv_mul_le : b ∈ closedBall a r ↔ ‖b⁻¹ * a‖ ≤ r := by sorry
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by sorry
theorem mem_closedBall_iff_norm_inv_mul_le' : b ∈ closedBall a r ↔ ‖a⁻¹ * b‖ ≤ r := by sorry
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by sorry
lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * ‖v‖ := by sorry
lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * min ‖u‖ ‖v‖ := by sorry
theorem mem_sphere_iff_norm_inv_mul_eq : b ∈ sphere a r ↔ ‖b⁻¹ * a‖ = r := by sorry
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2

@[to_additive]
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero <| by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive /-- The norm of a seminormed group as an additive group seminorm. -/]
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl

variable {E}

@[to_additive]
theorem NormedGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ‖f x‖ < ε :=
  Metric.tendsto_nhds.trans <| by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]
theorem NormedGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x'⁻¹ * x‖ < δ → ‖(f x')⁻¹ * y‖ < ε := by sorry
theorem NormedGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε } := by sorry
theorem NormedGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y‖ < ε } := by sorry
theorem NormedGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ < ε } := by sorry
open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ := rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl

@[to_additive (attr := simp) norm_toNNReal]
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]
lemma toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖ := by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
lemma ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by sorry
theorem enorm'_eq_iff_norm_eq {x : E} {y : F} : ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖ := by sorry
theorem enorm'_le_iff_norm_le {x : E} {y : F} : ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖ ≤ ‖y‖ := by sorry
theorem nndist_eq_nnnorm_inv_mul (a b : E) : nndist a b = ‖a⁻¹ * b‖₊ :=
  NNReal.eq <| dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a

@[to_additive (attr := simp)]
theorem nndist_one_right (a : E) : nndist a 1 = ‖a‖₊ := by sorry
lemma edist_one_right (a : E) : edist a 1 = ‖a‖ₑ := by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 := NNReal.eq norm_one'

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b

@[to_additive norm_nsmul_le]
lemma norm_pow_le_mul_norm : ∀ {n : ℕ}, ‖a ^ n‖ ≤ n * ‖a‖ := by sorry
lemma nnnorm_pow_le_mul_norm {n : ℕ} : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by sorry
theorem nnnorm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]
theorem nnnorm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]
theorem nnnorm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_zpow_isUnit a hn

@[simp]
theorem nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]
theorem nndist_one_left (a : E) : nndist 1 a = ‖a‖₊ := by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
theorem edist_one_left (a : E) : edist 1 a = ‖a‖₊ := by sorry
open scoped symmDiff in
@[to_additive]
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _

@[to_additive]
lemma enorm_div_le : ‖a / b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by sorry
theorem nndist_nnnorm_nnnorm_le_nnnorm_inv_mul (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a⁻¹ * b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le_norm_inv_mul a b

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ ≤ ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ ≤ ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ ≤ ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _

/-- An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `nnnorm_le_add_nnnorm_add` for the addition from the left. -/]
theorem nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ ≤ ‖a * b‖₊ + ‖a‖₊ :=
  norm_le_mul_norm_add' _ _

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_left _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_div_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_div_eq_norm_left _ <| congr_arg NNReal.toReal h

/-- The nonnegative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm /-- The nonnegative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm. -/]
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : ℝ≥0∞).toReal = ‖a‖ := rfl

open scoped symmDiff in
@[to_additive]
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by sorry
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖₊ ≠ 0 := by sorry
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖₊ = 0 := by sorry
variable (E) in
@[to_additive exists_nnnorm_ne_zero]
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖₊ ≠ 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖ ≠ 0 := by sorry
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖ = 0 := by sorry
variable (E) in
@[to_additive exists_norm_ne_zero]
theorem exists_norm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖ ≠ 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

section ENorm

@[to_additive (attr := simp) enorm_zero]
lemma enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : E)‖ₑ = 0 := by sorry
lemma exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
    [hbot : NeBot (𝓝[≠] (1 : E))] {c : ℝ≥0∞} (hc : c ≠ 0) : ∃ x ≠ (1 : E), ‖x‖ₑ < c :=
  frequently_iff_neBot.mpr hbot |>.and_eventually
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt) := by sorry
lemma enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ := by simp [enorm]

@[to_additive ofReal_norm_eq_enorm]
lemma ofReal_norm_eq_enorm' (a : E) : .ofReal ‖a‖ = ‖a‖ₑ := ENNReal.ofReal_eq_coe_nnreal _

@[to_additive]
theorem edist_eq_enorm_inv_mul (a b : E) : edist a b = ‖a⁻¹ * b‖ₑ := by sorry
lemma enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / a‖ₑ := by sorry
theorem mem_eball_one_iff {r : ℝ≥0∞} : a ∈ eball 1 r ↔ ‖a‖ₑ < r := by sorry
end ENorm

section ESeminormedMonoid

variable {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]

@[to_additive enorm_add_le]
lemma enorm_mul_le' (a b : E) : ‖a * b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]
theorem enorm_mul_le_of_le' {r₁ r₂ : ℝ≥0∞} {a₁ a₂ : E}
    (h₁ : ‖a₁‖ₑ ≤ r₁) (h₂ : ‖a₂‖ₑ ≤ r₂) : ‖a₁ * a₂‖ₑ ≤ r₁ + r₂ :=
  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

@[to_additive enorm_add₃_le]
lemma enorm_mul₃_le' {a b c : E} : ‖a * b * c‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ :=
  enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]
lemma enorm_mul₄_le' {a b c d : E} : ‖a * b * c * d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

end ESeminormedMonoid

section ENormedMonoid

variable {E : Type*} [TopologicalSpace E] [ENormedMonoid E]

@[to_additive (attr := simp) enorm_eq_zero]
lemma enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1 := by sorry
lemma enorm_ne_zero' {a : E} : ‖a‖ₑ ≠ 0 ↔ a ≠ 1 :=
  enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]
lemma enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a ≠ 1 :=
  pos_iff_ne_zero.trans enorm_ne_zero'

end ENormedMonoid

open Set in
@[to_additive]
lemma SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) :
    Disjoint (𝓝 x) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y⁻¹ * x‖ := by sorry
lemma SeminormedGroup.disjoint_nhds_one (f : Filter E) :
    Disjoint (𝓝 1) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y‖ := by sorry
end SeminormedGroup

section Induced

variable (E F)
variable [FunLike 𝓕 E F]

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain. -/]
abbrev SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain. -/]
abbrev SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
structure on the domain. -/
@[to_additive /-- An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain. -/]
abbrev NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive /-- An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain. -/]
abbrev NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ := by sorry
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by sorry
theorem norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖ := by sorry
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a / b‖ :=
  (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a / b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le' a b

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]
theorem edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ := by sorry
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by sorry
theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero.le norm_add_le

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
theorem enorm_multisetSum_le (m : Multiset ε) :
    ‖m.sum‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε] in
@[to_additive existing]
theorem enorm_multisetProd_le (m : Multiset ε) :
    ‖m.prod‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
@[bound]
theorem enorm_sum_le (s : Finset ι) (f : ι → ε) :
    ‖∑ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]
theorem enorm_prod_le (s : Finset ι) (f : ι → ε) : ‖∏ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]
theorem enorm_prod_le_of_le (s : Finset ι) {f : ι → ε} {n : ι → ℝ≥0∞} (h : ∀ b ∈ s, ‖f b‖ₑ ≤ n b) :
    ‖∏ b ∈ s, f b‖ₑ ≤ ∑ b ∈ s, n b :=
  (enorm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b ∈ s, f b‖ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, d b := by sorry
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ‖x / y‖ < ε } := by sorry
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ‖b / a‖ < r := by sorry
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ‖a / b‖ < r := by sorry
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by sorry
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by sorry
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by sorry
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by sorry
theorem preimage_mul_ball (a b : E) (r : ℝ) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by sorry
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by sorry
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by sorry
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by sorry
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by sorry
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by sorry
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by sorry
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by sorry
theorem smul_ball'' : a • ball b r = ball (a • b) r := by sorry
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b ∈ s, f b‖₊ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x' / x‖ < δ → ‖f x' / y‖ < ε := by sorry
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by sorry
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by sorry
end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

@[to_additive (attr := simp) norm_le_zero_iff]
lemma norm_le_zero_iff' : ‖a‖ ≤ 0 ↔ a = 1 := by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]
lemma norm_pos_iff' : 0 < ‖a‖ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]
lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]
lemma norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 := norm_eq_zero'.not

@[to_additive]
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero', div_eq_one]

@[to_additive]
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by sorry
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by sorry
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by sorry
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by sorry
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a ≠ 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive /-- The norm of a normed group as an additive group norm. -/]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `HasCompactSupport` -/

theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

end NormedAddGroup

/-! ### `positivity` extensions -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are always nonnegative, and positive
on non-one inputs. -/
@[positivity ‖_‖]
meta def evalMulNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedGroup_E ← synthInstanceQ q(SeminormedGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 1` assumption
    let o : Option (Q(NormedGroup $E) × Q($a ≠ 1)) := ← do
      let .some normedGroup_E ← trySynthInstanceQ q(NormedGroup $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 1) | return none
      return some (normedGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff'.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg' $a)
  | _, _, _ => throwError "not `‖·‖`"

/-- Extension for the `positivity` tactic: additive norms are always nonnegative, and positive
on non-zero inputs. -/
@[positivity ‖_‖]
meta def evalAddNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedAddGroup_E ← synthInstanceQ q(SeminormedAddGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 0` assumption
    let o : Option (Q(NormedAddGroup $E) × Q($a ≠ 0)) := ← do
      let .some normedAddGroup_E ← trySynthInstanceQ q(NormedAddGroup $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 0) | return none
      return some (normedAddGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedAddGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg $a)
  | _, _, _ => throwError "not `‖·‖`"

end Mathlib.Meta.Positivity
