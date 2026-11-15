-- Statement-only formalization of Thousand Theorems artifact Q282649
-- (thousand-theorems__lean4__Q282649), "Pentagonal number theorem": the infinite
-- product of the power series 1 - X^(n + 1) equals the pentagonal-number series.
-- This file contains no proof.

module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.PowerSeries.PiTopology

@[expose] public section

open Filter PowerSeries WithPiTopology

open scoped Topology

namespace Q282649

variable (R : Type*) [CommRing R]

/-- The generalized pentagonal number `k * (3 * k - 1) / 2`. -/
def pentagonal (k : ℤ) : ℕ :=
  (k * (3 * k - 1) / 2).toNat

open Classical in
/-- The signed power series supported on the generalized pentagonal numbers. -/
noncomputable def pentagonalSeries : R⟦X⟧ :=
  .mk fun n ↦ if h : ∃ k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

variable [TopologicalSpace R]

/-- The pentagonal number theorem for formal power series, expressed as an infinite product. -/
theorem pentagonal_number_theorem_statement :
    HasProd (fun n ↦ (1 - X ^ (n + 1) : R⟦X⟧)) (pentagonalSeries R) := sorry

end Q282649
