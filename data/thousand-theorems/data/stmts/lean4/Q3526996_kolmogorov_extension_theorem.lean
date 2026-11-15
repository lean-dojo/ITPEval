-- Statement-only formalization of Thousand Theorems artifact Q3526996
-- (thousand-theorems__lean4__Q3526996), "Kolmogorov extension theorem": every
-- projective family of finite measures on finite products of Polish spaces has
-- a projective-limit measure on the full product. This file contains no proof.

module

public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}
  [∀ I, IsFiniteMeasure (P I)]

/-- Sigma-subadditivity needed to construct the projective-limit measure from
the projective-family content. -/
theorem projectiveFamilyContent_iUnion_le_sum_Q3526996
    (hP : IsProjectiveMeasureFamily P)
    ⦃f : ℕ → Set (Π i, α i)⦄
    (hf : ∀ i, f i ∈ measurableCylinders α)
    (hf_Union : (⋃ i, f i) ∈ measurableCylinders α) :
    projectiveFamilyContent hP (⋃ i, f i) ≤
      ∑' i, projectiveFamilyContent hP (f i) := sorry

/-- The canonical projective-limit measure obtained from the projective-family content. -/
noncomputable def projectiveLimit_Q3526996
    (P : ∀ J : Finset ι, Measure (Π j : J, α j))
    [∀ I, IsFiniteMeasure (P I)] (hP : IsProjectiveMeasureFamily P) :
    Measure (Π i, α i) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm.le
    (projectiveFamilyContent_iUnion_le_sum_Q3526996 hP)

/-- The Kolmogorov extension theorem: the canonical projective-limit measure
has the prescribed finite-dimensional marginals. -/
theorem isProjectiveLimit_projectiveLimit_Q3526996
    (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit_Q3526996 P hP) P := sorry

end MeasureTheory
