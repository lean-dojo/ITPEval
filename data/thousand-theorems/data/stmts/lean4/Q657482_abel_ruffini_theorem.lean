-- Statement-only formalization of Thousand Theorems artifact Q657482
-- (thousand-theorems__lean4__Q657482), "Abel–Ruffini theorem": there exists a
-- complex number algebraic over the rationals that is not solvable by radicals
-- over the rationals. This file contains no proof.

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.AbelRuffini

namespace AbelRuffini

/-- Some complex algebraic number over `ℚ` is not solvable by radicals over `ℚ`. -/
theorem exists_not_solvable_by_rad :
    ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := sorry

end AbelRuffini
