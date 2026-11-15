-- Statement-only formalization of Thousand Theorems artifact Q791663
-- (thousand-theorems__lean4__Q791663), "Beatty's theorem": for Holder-conjugate
-- real parameters, the complement of one two-sided Beatty sequence is the
-- ceiling variant of the other, and for irrational r the positive Beatty
-- sequences partition the positive integers. This file contains no proof.

module

public import Mathlib.Data.Real.ConjExponents
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-- In the Beatty sequence for `r`, the term indexed by `k` is `floor (k * r)`. -/
noncomputable def beattySeq (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌊k * r⌋

/-- This Beatty-sequence variant has term `ceil (k * r) - 1` at index `k`. -/
noncomputable def beattySeq' (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌈k * r⌉ - 1

/-- The complement of one two-sided Beatty sequence is the conjugate ceiling variant. -/
theorem compl_beattySeq {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k}ᶜ = {beattySeq' s k | k} := sorry

open scoped symmDiff

/-- Irrational conjugate positive Beatty sequences partition the positive integers. -/
theorem Irrational.beattySeq_symmDiff_beattySeq_pos {r s : ℝ}
    (hrs : r.HolderConjugate s) (hr : Irrational r) :
    {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := sorry
