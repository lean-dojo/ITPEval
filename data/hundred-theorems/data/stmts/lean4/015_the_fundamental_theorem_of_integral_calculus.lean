/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Fundamental Theorem of Calculus

We prove various versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for interval integrals in `ℝ`.

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `intervalIntegral` namespace. Many of them follow
the naming scheme `integral_has(Strict?)(F?)Deriv(Within?)At(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `Has(Strict?)(F?)Deriv(Within?)At`.
Let us explain the meaning of each part of the name:

* `Strict` means that the theorem is about strict differentiability, see `HasStrictDerivAt` and
  `HasStrictFDerivAt`;
* `F` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `Within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(Within?)`. These theorems are named
`(f?)deriv(Within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae` states that
`(u, v) ↦ ∫ x in u..v, f x` has a derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t`
at `(a, b)` provided that `f` tends to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where
possible values of `s`, `t`, and corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `intervalIntegral.FTCFilter` to make Lean automatically find `la`/`lb` based on
`s`/`t`. This way we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial
ones not covered by `integral_hasDerivWithinAt_of_tendsto_ae_(left|right)` and
`integral_hasFDerivAt_of_tendsto_ae`). Similarly, `integral_hasDerivWithinAt_of_tendsto_ae_right`
works for both one-sided derivatives using the same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae`, states the following.
Let `(la, la')` be an `intervalIntegral.FTCFilter` pair of filters around `a` (i.e.,
`intervalIntegral.FTCFilter a la la'`) and let `(lb, lb')` be an `intervalIntegral.FTCFilter` pair
of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at `la'` and `lb'`,
respectively, then
$$
  \int_{va}^{vb} f ∂μ - \int_{ua}^{ub} f ∂μ =
  \int_{ub}^{vb} cb ∂μ - \int_{ua}^{va} ca ∂μ + o(‖∫_{ua}^{va} 1 ∂μ‖ + ‖∫_{ub}^{vb} (1:ℝ) ∂μ‖)
$$
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` - most general version, for functions
  with a right derivative
* `intervalIntegral.integral_eq_sub_of_hasDerivAt` - version for functions with a derivative on
  an open set
* `intervalIntegral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

Many applications of these theorems can be found in the directory
`Mathlib/Analysis/SpecialFunctions/Integrals/`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`ContinuousOn.intervalIntegrable` or `ContinuousOn.integrableOn_Icc` or
`ContinuousOn.integrableOn_uIcc`.

Versions of FTC-2 under the simpler assumption that the function is `C^1` are given in the
file `Mathlib/MeasureTheory/Integral/IntervalIntegral/ContDiff.lean`.

Applications to integration by parts are in the file
`Mathlib.MeasureTheory.Integral.IntegrationByParts`.

### `intervalIntegral.FTCFilter` class

As explained above, many theorems in this file rely on the typeclass
`intervalIntegral.FTCFilter (a : ℝ) (l l' : Filter ℝ)` to avoid code duplication. This typeclass
combines four assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `intervalIntegral.FTCFilter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Set.Icc a b] x, 𝓝[Set.Icc a b] x)` (resp.
`(x, 𝓝[Set.uIcc a b] x, 𝓝[Set.uIcc a b] x)`), with `x ∈ Icc a b` (resp. `x ∈ uIcc a b`). This
results in a two-sided derivatives for `x ∈ Set.Ioo a b` and one-sided derivatives for `x ∈ {a, b}`.
Other instances could be added when needed (in that case, one also needs to add instances for
`Filter.IsMeasurablyGenerated` and `Filter.TendstoIxxClass`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2
-/

@[expose] public section

assert_not_exists HasDerivAt.mul -- guard against import creep

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace intervalIntegral

section FTC1

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`intervalIntegral.FTCFilter a l l'`. This typeclass has exactly four “real” instances:
`(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` can be
seen as a generalization of lemma `integral_hasStrictFDerivAt` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right-hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`. -/
class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) : Prop
    extends TendstoIxxClass Ioc outer inner where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]

namespace FTCFilter


instance pure (a : ℝ) : FTCFilter a (pure a) ⊥ where
  pure_le := le_rfl
  le_nhds := bot_le

instance nhdsWithinSingleton (a : ℝ) : FTCFilter a (𝓝[{a}] a) ⊥ := by sorry
theorem finiteAt_inner {a : ℝ} (l : Filter ℝ) {l'} [h : FTCFilter a l l'] {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] : μ.FiniteAtFilter l' :=
  (μ.finiteAt_nhds a).filter_mono h.le_nhds

instance nhds (a : ℝ) : FTCFilter a (𝓝 a) (𝓝 a) where
  pure_le := pure_le_nhds a
  le_nhds := le_rfl

instance nhdsUniv (a : ℝ) : FTCFilter a (𝓝[univ] a) (𝓝 a) := by rw [nhdsWithin_univ]; infer_instance

instance nhdsLeft (a : ℝ) : FTCFilter a (𝓝[≤] a) (𝓝[≤] a) where
  pure_le := pure_le_nhdsWithin self_mem_Iic
  le_nhds := inf_le_left

instance nhdsRight (a : ℝ) : FTCFilter a (𝓝[≥] a) (𝓝[>] a) where
  pure_le := pure_le_nhdsWithin self_mem_Ici
  le_nhds := inf_le_left

instance nhdsIcc {x a b : ℝ} [h : Fact (x ∈ Icc a b)] :
    FTCFilter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) where
  pure_le := pure_le_nhdsWithin h.out
  le_nhds := inf_le_left

instance nhdsUIcc {x a b : ℝ} [h : Fact (x ∈ [[a, b]])] :
    FTCFilter x (𝓝[[[a, b]]] x) (𝓝[[[a, b]]] x) :=
  .nhdsIcc (h := h)

end FTCFilter

section

variable {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι}
  {μ : Measure ℝ} {u v ua va ub vb : ι → ℝ}

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l' ⊓ ae μ`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.  The primed version
also works, e.g., for `l = l' = atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ := by sorry
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf hl hu hv).congr'
    (huv.mono fun x hx => by simp [integral_const', hx])
    (huv.mono fun x hx => by simp [integral_const', hx])

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. The primed version
also works, e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf hl hv hu
          huv).neg_left.congr_left
    fun t => by simp [integral_symm (u t), add_comm]

section IsLocallyFiniteMeasure

variable [IsLocallyFiniteMeasure μ]

variable [FTCFilter a la la'] [FTCFilter b lb lb']

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae'` for a version that also works, e.g.,
for `l = l' = Filter.atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf (FTCFilter.finiteAt_inner l) hu hv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = -μ (Set.Ioc v u) • c + o(μ(Set.Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f la' μ)
    (hmeas_b : StronglyMeasurableAtFilter f lb' μ) (ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) -
          ((∫ _ in ub t..vb t, cb ∂μ) - ∫ _ in ua t..va t, ca ∂μ)) =o[lt]
      fun t => ‖∫ _ in ua t..va t, (1 : ℝ) ∂μ‖ + ‖∫ _ in ub t..vb t, (1 : ℝ) ∂μ‖ := by sorry
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f lb' μ)
    (hf : Tendsto f (lb' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by sorry
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f la' μ)
    (hf : Tendsto f (la' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by sorry
end IsLocallyFiniteMeasure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/


variable [CompleteSpace E]
  {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {a b : ℝ}
  {u v ua ub va vb : ι → ℝ} [FTCFilter a la la'] [FTCFilter b lb lb']

/-!
#### Auxiliary `Asymptotics.IsLittleO` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use
`Asymptotics.isLittleO` because we have no definition of `HasStrict(F)DerivAtFilter` in the library.
-/


/-- **Fundamental theorem of calculus-1**, local version.

If `f` has a finite limit `c` almost surely at `l'`, where `(l, l')` is an
`intervalIntegral.FTCFilter` pair around `a`, then `∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)`
as both `u` and `v` tend to `l`. -/
theorem integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l') (hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)) {u v : ι → ℝ}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x) - (v t - u t) • c) =o[lt] (v - u) := by sorry
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la')
    (hmeas_b : StronglyMeasurableAtFilter f lb') (ha_lim : Tendsto f (la' ⊓ ae volume) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) -
          ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt]
      fun t => ‖va t - ua t‖ + ‖vb t - ub t‖ := by sorry
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f lb')
    (hf : Tendsto f (lb' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt] (v - u) := by sorry
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f la')
    (hf : Tendsto f (la' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] (v - u) := by sorry
open ContinuousLinearMap (fst snd smulRight sub_apply smulRight_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_hasStrictFDerivAt_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tends to `a` and `b`,
  respectively;

* `integral_hasStrictFDerivAt`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_hasStrictDerivAt_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_hasStrictDerivAt_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/


/-- **Fundamental theorem of calculus-1**, strict differentiability in both endpoints.

If `f : ℝ → E` is integrable on `a..b` and `f x` has finite limits `ca` and `cb` almost surely as
`x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
theorem integral_hasStrictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) := by sorry
theorem integral_hasStrictFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `b`, then
`u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b :=
  .of_isLittleO <|
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb continuousAt_snd
      continuousAt_fst

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `b`, then `u ↦ ∫ x in a..u, f x` has
derivative `f b` at `b` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the left endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `a`, then
`u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a := by sorry
theorem integral_hasStrictDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-f a) a := by sorry
theorem _root_.Continuous.integral_hasStrictDerivAt {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    HasStrictDerivAt (fun u => ∫ x : ℝ in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

/-- **Fundamental theorem of calculus-1**, derivative in the right endpoint.

If `f : ℝ → E` is continuous, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` is `f b`. -/
theorem _root_.Continuous.deriv_integral (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `HasFDerivAt`,
`HasDerivAt`, `fderiv`, and `deriv`.
-/


/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
theorem integral_hasFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) :=
  (integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u •
ca` at `(a, b)`. -/
theorem integral_hasFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  (integral_hasStrictFDerivAt hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)`
equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a) :=
  (integral_hasFDerivAt hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
theorem integral_hasDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in a..u, f x) c b :=
  (integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas hb).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_hasStrictDerivAt_right hf hmeas hb).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in a..u, f x) b = c :=
  (integral_hasDerivAt_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_integral_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    deriv (fun u => ∫ x in a..u, f x) b = f b :=
  (integral_hasDerivAt_right hf hmeas hb).deriv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
theorem integral_hasDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a :=
  (integral_hasStrictDerivAt_of_tendsto_ae_left hf hmeas ha).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
theorem integral_hasDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-f a) a :=
  (integral_hasStrictDerivAt_left hf hmeas ha).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in u..b, f x) a = -c :=
  (integral_hasDerivAt_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_integral_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : ContinuousAt f a) :
    deriv (fun u => ∫ x in u..b, f x) a = -f a :=
  (integral_hasDerivAt_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/


/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.
 := by sorry
theorem integral_hasFDerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (s ×ˢ t) (a, b) := by sorry
theorem integral_hasFDerivWithinAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tendsto f la (𝓝 <| f a))
    (hb : Tendsto f lb (𝓝 <| f b)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (s ×ˢ t) (a, b) :=
  integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `UniqueDiffWithinAt ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
macro "uniqueDiffWithinAt_Ici_Iic_univ" : tactic =>
  `(tactic| (first | exact uniqueDiffOn_Ici _ _ self_mem_Ici |
    exact uniqueDiffOn_Iic _ _ self_mem_Iic | exact uniqueDiffWithinAt_univ (𝕜 := ℝ) (E := ℝ)))

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderivWithin ℝ (fun p ↦ ∫ x in p.1..p.2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.
 := by sorry
theorem fderivWithin_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ)
    (ht : UniqueDiffWithinAt ℝ t b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    fderivWithin ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (s ×ˢ t) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderivWithin <| hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
theorem integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in a..u, f x) c s b :=
  .of_isLittleO <| integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb
    (tendsto_const_pure.mono_right FTCFilter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
theorem integral_hasDerivWithinAt_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b) : HasDerivWithinAt (fun u => ∫ x in a..u, f x) (f b) s b :=
  integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem derivWithin_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem derivWithin_integral_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b)
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = f b :=
  (integral_hasDerivWithinAt_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
theorem integral_hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-c) s a := by sorry
theorem integral_hasDerivWithinAt_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a) : HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-f a) s a :=
  integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem derivWithin_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas ha).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem derivWithin_integral_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a)
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -f a :=
  (integral_hasDerivWithinAt_left hf hmeas ha).derivWithin hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_integral_of_continuous (hcont : Continuous f) :
    Differentiable ℝ (fun u => ∫ x in a..u, f x) := fun _ ↦
  (integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).differentiableAt

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiableOn_integral_of_continuous {s : Set ℝ} (hcont : Continuous f) :
    DifferentiableOn ℝ (fun u => ∫ x in a..u, f x) s :=
  (differentiable_integral_of_continuous hcont).differentiableOn

end FTC1

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left-hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right-hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

section FTC2

variable {g' g φ : ℝ → ℝ} {a b : ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`. -/
theorem sub_le_integral_of_hasDeriv_right_of_le_Ico (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (φint : IntegrableOn φ (Icc a b)) (hφg : ∀ x ∈ Ico a b, g' x ≤ φ x) :
    g b - g a ≤ ∫ y in a..b, φ y := by sorry
theorem sub_le_integral_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by sorry
theorem integral_le_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, φ x ≤ g' x) : (∫ y in a..b, φ y) ≤ g b - g a := by sorry
theorem integral_eq_sub_of_hasDeriv_right_of_le_real (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'int : IntegrableOn g' (Icc a b)) : ∫ y in a..b, g' y = g b - g a :=
  le_antisymm (integral_le_sub_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)
    (sub_le_integral_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)

variable [CompleteSpace E] {f f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by sorry
theorem integral_eq_sub_of_hasDeriv_right (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by sorry
theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivWithinAt)
    hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right (HasDerivAt.continuousOn hderiv)
    (fun _x hx => (hderiv _ (mem_Icc_of_Ioo hx)).hasDerivWithinAt) hint

theorem integral_eq_sub_of_hasDerivAt_of_tendsto (hab : a < b) {fa fb}
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    ∫ y in a..b, f' y = fb - fa := by sorry
theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hderiv x hx).hasDerivAt) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
    (hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x) (hcont : ContinuousOn f' (uIcc a b)) :
    ∫ y in a..b, f' y = f b - f a := by sorry
theorem integral_deriv_eq_sub_uIoo
    (hcont : ContinuousOn f [[a, b]]) (hderiv : ∀ x ∈ uIoo a b, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a := by sorry
lemma integral_unitInterval_deriv_eq_sub [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    {f f' : 𝕜 → E} {z₀ z₁ : 𝕜}
    (hcont : ContinuousOn (fun t : ℝ ↦ f' (z₀ + t • z₁)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) :
    z₁ • ∫ t in (0 : ℝ)..1, f' (z₀ + t • z₁) = f (z₀ + z₁) - f z₀ := by sorry
theorem integrableOn_deriv_right_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) : IntegrableOn g' (Ioc a b) := by sorry
theorem integrableOn_deriv_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) :=
  integrableOn_deriv_right_of_nonneg hcont (fun x hx => (hderiv x hx).hasDerivWithinAt) g'pos

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
interval version. -/
theorem intervalIntegrable_deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ g' x) : IntervalIntegrable g' volume a b := by sorry
end FTC2

end intervalIntegral
