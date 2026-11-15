-- Statement-only formalization of Thousand Theorems artifact Q190556
-- (thousand-theorems__lean4__Q190556), "De Moivre's theorem": raising
-- `cos z + sin z * I` to a natural-number power multiplies the complex
-- argument by that natural number. This file contains no proof.

module

public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

namespace Q190556

/-- De Moivre's formula for complex sine and cosine. -/
theorem de_moivre_s_theorem (n : ℕ) (z : ℂ) :
    (Complex.cos z + Complex.sin z * Complex.I) ^ n =
      Complex.cos (↑n * z) + Complex.sin (↑n * z) * Complex.I := sorry

end Q190556
