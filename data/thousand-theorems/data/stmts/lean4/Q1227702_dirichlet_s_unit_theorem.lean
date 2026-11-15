-- Statement-only formalization of Thousand Theorems artifact Q1227702
-- (thousand-theorems__lean4__Q1227702), "Dirichlet's unit theorem": the unit group
-- modulo torsion has a finite integral basis, and every unit is uniquely a root
-- of unity times integral powers of the associated fundamental units. This file contains no proof.

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

noncomputable section

open Module NumberField

namespace Q1227702

variable (K : Type*) [Field K] [NumberField K]

/-- The source basis of the unit group modulo torsion. -/
abbrev basisModTorsion := NumberField.Units.basisModTorsion K

/-- Dirichlet's unit theorem in its unique fundamental-unit decomposition form. -/
theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) :
    ∃! ζe : NumberField.Units.torsion K ×
        (Fin (NumberField.Units.rank K) → ℤ),
      x = ζe.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ (ζe.2 i) := sorry

end Q1227702
