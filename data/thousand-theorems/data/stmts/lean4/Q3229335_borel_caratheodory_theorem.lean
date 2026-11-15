-- Canonical Lean registration for Thousand Theorems artifact Q3229335,
-- "Borel-Caratheodory theorem". The statement is copied exactly from
-- the imported `Complex.borelCaratheodory`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Complex.BorelCaratheodory

@[expose] public section

namespace ThousandTheorems.Q3229335

/-- The Mathlib statement selected as the canonical Lean form of Borel-Caratheodory theorem. -/
theorem canonical_statement : type_of% @Complex.borelCaratheodory :=
  @Complex.borelCaratheodory

end ThousandTheorems.Q3229335
