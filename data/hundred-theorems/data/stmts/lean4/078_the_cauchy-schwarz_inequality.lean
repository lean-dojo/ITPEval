/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Properties of inner product spaces

This file proves many basic properties of inner product spaces (real or complex).

## Main results

- `inner_mul_inner_self_le`: the Cauchy-Schwarz inequality (one of many variants).
- `norm_inner_eq_norm_iff`: the equality criterion in the Cauchy-Schwarz inequality (also in many
  variants).
- `inner_eq_sum_norm_sq_div_four`: the polarization identity.

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

@[simp]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_inner_symm _ _

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_symm ℝ _ _ _ _ x y

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by sorry
instance {ι : Sort*} (v : ι → E) : Std.Symm fun i j => ⟪v i, v j⟫ = 0 where
  symm _ _ := inner_eq_zero_symm.1

theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by sorry
theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by sorry
theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

section Algebra
variable {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [Module 𝕝 E]
  [IsScalarTower 𝕝 𝕜 E] [StarModule 𝕝 𝕜]

/-- See `inner_smul_left` for the common special when `𝕜 = 𝕝`. -/
lemma inner_smul_left_eq_star_smul (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫ := by sorry
lemma inner_smul_left_eq_smul [TrivialStar 𝕝] (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r • ⟪x, y⟫ := by sorry
lemma inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪x, r • y⟫ = r • ⟪x, y⟫ := by sorry
end Algebra

/-- See `inner_smul_left_eq_star_smul` for the case of a general algebra action. -/
theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left_eq_star_smul ..

theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _

theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by sorry
theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right_eq_smul ..

theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _

theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by sorry
variable (𝕜)

/-- The inner product as a sesquilinear map.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]
theorem coe_innerₛₗ_apply (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/-- The inner product as a bilinear map in the real case. -/
def innerₗ : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := innerₛₗ ℝ

@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by sorry
variable {F}

@[simp] lemma innerₗ_apply_apply (v w : F) : innerₗ F v w = ⟪v, w⟫_ℝ := rfl

variable {𝕜}

@[deprecated (since := "2025-12-26")] alias sesqFormOfInner := innerₛₗ
@[deprecated (since := "2025-12-26")] noncomputable alias bilinFormOfRealInner := innerₗ

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum ((innerₛₗ 𝕜).flip x) _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (innerₛₗ 𝕜 x) _ _

/-- An inner product with a sum on the left, `Finsupp` version. -/
protected theorem Finsupp.sum_inner {ι : Type*} {M : Type*} [Zero M] (l : ι →₀ M)
    (v : ι → M → E) (x : E) : ⟪l.sum v, x⟫ = l.sum fun (i : ι) (a : M) ↦ ⟪v i a, x⟫ := by sorry
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by sorry
theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by sorry
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by sorry
theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by sorry
theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  PreInnerProductSpace.toCore.re_inner_nonneg x

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x

theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

@[simp]
theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2 := by sorry
theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ := by sorry
theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫ := by sorry
theorem real_inner_self_abs (x : F) : |⟪x, x⟫_ℝ| = ⟪x, x⟫_ℝ :=
  @inner_self_ofReal_norm ℝ F _ _ _ x

theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

@[simp]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by sorry
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by sorry
theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by sorry
theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by sorry
theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by sorry
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by sorry
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by sorry
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by sorry
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by sorry
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by sorry
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
  calc
    ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ‖⟪x, y⟫_ℝ‖ * ‖⟪y, x⟫_ℝ‖ := by sorry
theorem inner_eq_ofReal_norm_sq_left_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0 := by sorry
theorem inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_ℝ = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_left_iff

theorem inner_eq_ofReal_norm_sq_right_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0 := by sorry
theorem inner_eq_norm_sq_right_iff {v w : F} : ⟪v, w⟫_ℝ = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_right_iff

end BasicProperties_Seminormed

section BasicProperties

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

export InnerProductSpace (norm_sq_eq_re_inner)

theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by sorry
theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

variable (𝕜)

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by sorry
theorem ext_iff_inner_left {x y : E} : x = y ↔ ∀ v, ⟪v, x⟫ = ⟪v, y⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_left 𝕜⟩

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by sorry
theorem ext_iff_inner_right {x y : E} : x = y ↔ ∀ v, ⟪x, v⟫ = ⟪y, v⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_right 𝕜⟩

variable {𝕜}

theorem re_inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by sorry
lemma re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x ≠ 0 := by sorry
open scoped InnerProductSpace in
theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 := re_inner_self_nonpos (𝕜 := ℝ)

open scoped InnerProductSpace in
theorem real_inner_self_pos {x : F} : 0 < ⟪x, x⟫_ℝ ↔ x ≠ 0 := re_inner_self_pos (𝕜 := ℝ)

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v := by sorry
end BasicProperties

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "IK" => @RCLike.I 𝕜 _

theorem norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫) :=
  calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)

theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫_ℝ :=
  @norm_eq_sqrt_re_inner ℝ _ _ _ _ x

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by sorry
theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by sorry
theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ := by sorry
theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by sorry
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by sorry
theorem norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by sorry
theorem norm_add_mul_self (x y : E) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by sorry
theorem norm_add_mul_self_real (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by sorry
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by sorry
theorem norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  @norm_sub_sq ℝ _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

/-- Expand the square -/
theorem norm_sub_mul_self (x y : E) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by sorry
theorem norm_sub_mul_self_real (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by sorry
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by sorry
theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y

theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ :=
  (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

lemma inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by sorry
lemma inner_eq_zero_of_right (x : E) {y : E} (h : ‖y‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by sorry
variable (𝕜)

include 𝕜 in
theorem parallelogram_law_with_norm_mul (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by sorry
theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by sorry
theorem parallelogram_law_with_nnnorm_mul (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm_mul 𝕜 x y

include 𝕜 in
theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ ^ 2 + ‖x - y‖₊ ^ 2 = 2 * (‖x‖₊ ^ 2 + ‖y‖₊ ^ 2) := by sorry
variable {𝕜}

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by sorry
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by sorry
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by sorry
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by sorry
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 +
              ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x + IK • y‖ : 𝕜) ^ 2) * IK) / 4 := by sorry
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by sorry
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by sorry
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := by sorry
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by sorry
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by sorry
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ := by sorry
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ := by sorry
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| ≤ 1 := by sorry
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) := by sorry
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) := by sorry
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : ∑ i ∈ s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : ∑ i ∈ s₂, w₂ i = 0) :
    ⟪∑ i₁ ∈ s₁, w₁ i₁ • v₁ i₁, ∑ i₂ ∈ s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
      (-∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 := by sorry
end Norm_Seminormed

section Norm

open scoped InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `EuclideanGeometry.dist_inversion_inversion` for inversions around a general
point. -/
theorem dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y :=
  calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by sorry
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0)
    (hr : r ≠ 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 := by sorry
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ}
    (hx : x ≠ 0) (hr : r ≠ 0) : |⟪x, r • x⟫_ℝ| / (‖x‖ * ‖r • x‖) = 1 :=
  norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 := by sorry
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 := by sorry
variable (𝕜) in
theorem norm_inner_eq_norm_tfae (x y : E) :
    List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖,
      x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x,
      x = 0 ∨ ∃ r : 𝕜, y = r • x,
      x = 0 ∨ y ∈ 𝕜 ∙ x] := by sorry
theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ ∃ r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
      ⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ <| h.symm ▸ smul_eq_zero.2 <| Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x := by sorry
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) : := by sorry
theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x ≠ 0) :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y := by sorry
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y := by sorry
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by sorry
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by sorry
theorem inner_eq_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 ↔ x = y := by sorry
theorem inner_eq_neg_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = -1 ↔ x = -y := by sorry
theorem real_inner_le_one_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ ≤ 1 := by sorry
theorem neg_one_le_real_inner_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ ⟪x, y⟫_ℝ := by sorry
theorem real_inner_mem_Icc_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ ∈ Set.Icc (-1) 1 :=
  ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩

theorem inner_self_eq_one_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_𝕜 = 1 :=
  (inner_eq_one_iff_of_norm_eq_one hx hx).mpr rfl

theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
  calc
    ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x ≠ ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by convert inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

@[deprecated (since := "2025-11-15")] alias inner_eq_one_iff_of_norm_one :=
  inner_eq_one_iff_of_norm_eq_one
@[deprecated (since := "2025-11-15")] alias inner_self_eq_one_of_norm_one :=
  inner_self_eq_one_of_norm_eq_one
@[deprecated (since := "2025-11-15")] alias inner_lt_one_iff_real_of_norm_one :=
  inner_lt_one_iff_real_of_norm_eq_one

/-- The sphere of radius `r = ‖y‖` is tangent to the plane `⟪x, y⟫ = ‖y‖ ^ 2` at `x = y`. -/
theorem eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ ≤ ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) :
    x = y := by sorry
theorem norm_add_eq_iff_real {x y : F} : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y := by sorry
end Norm

section RCLike

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A field `𝕜` satisfying `RCLike` is itself a `𝕜`-inner product space. -/
instance RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜 where
  inner x y := y * conj x
  norm_sq_eq_re_inner x := by simp only [mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by simp only [mul_comm, map_mul, starRingEnd_self_apply]
  add_left x y z := by simp only [mul_add, map_add]
  smul_left x y z := by simp only [mul_comm (conj z), mul_assoc, smul_eq_mul, map_mul]

@[simp]
theorem RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x :=
  rfl

/-- A version of `RCLike.inner_apply` that swaps the order of multiplication. -/
theorem RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y := mul_comm _ _

end RCLike

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}
variable (𝕜 E)
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A general inner product implies a real inner product. This is not registered as an instance
since `𝕜` does not appear in the return type `Inner ℝ E`. -/
@[implicit_reducible]
def Inner.rclikeToReal : Inner ℝ E where inner x y := re ⟪x, y⟫

/-- A general inner product space structure implies a real inner product structure.

This is not registered as an instance since
* `𝕜` does not appear in the return type `InnerProductSpace ℝ E`,
* It is likely to create instance diamonds, as it builds upon the diamond-prone
  `NormedSpace.restrictScalars`.

However, it can be used in a proof to obtain a real inner product space structure from a given
`𝕜`-inner product space structure. -/
-- See note [reducible non-instances]
abbrev InnerProductSpace.rclikeToReal : InnerProductSpace ℝ E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp +instances only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      letI := NormedSpace.restrictScalars ℝ 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp +instances only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

variable {E}

theorem real_inner_eq_re_inner (x y : E) :
    (Inner.rclikeToReal 𝕜 E).inner x y = re ⟪x, y⟫ :=
  rfl

theorem real_inner_I_smul_self (x : E) :
    (Inner.rclikeToReal 𝕜 E).inner x ((I : 𝕜) • x) = 0 := by sorry
def InnerProductSpace.complexToReal [SeminormedAddCommGroup G] [InnerProductSpace ℂ G] :
    InnerProductSpace ℝ G :=
  InnerProductSpace.rclikeToReal ℂ G

instance : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal

@[simp]
protected theorem Complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (z * conj w).re :=
  rfl

end RCLikeToReal

/-- An `RCLike` field is a real inner product space. -/
noncomputable instance RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ 𝕜 where
  __ := Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by simp only [map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

-- The instance above does not create diamonds for concrete `𝕜`:
example : (innerProductSpace : InnerProductSpace ℝ ℝ) = RCLike.toInnerProductSpaceReal := rfl
example :
    (instInnerProductSpaceRealComplex : InnerProductSpace ℝ ℂ) = RCLike.toInnerProductSpaceReal :=
  rfl

section IsPosSemidef

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma isSymm_inner : LinearMap.IsSymm (innerₗ E) where
  eq x y := by simp [real_inner_comm]

lemma isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where
  nonneg x := by simp

lemma isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where
  isSymm := isSymm_inner
  isNonneg := isNonneg_inner

end IsPosSemidef
