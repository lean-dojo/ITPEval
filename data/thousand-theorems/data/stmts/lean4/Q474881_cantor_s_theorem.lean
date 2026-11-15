-- Statement-only formalization of Thousand Theorems artifact Q474881
-- (thousand-theorems__lean4__Q474881), "Cantor's theorem": no function from an
-- arbitrary type onto its power set is surjective. This file contains no proof.

import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs

universe u

namespace Q474881

/-- Cantor's theorem: no function from a type onto its power set is surjective. -/
theorem cantor_surjective_statement {α : Type u} (f : α → Set α) :
    ¬Function.Surjective f := sorry

end Q474881
