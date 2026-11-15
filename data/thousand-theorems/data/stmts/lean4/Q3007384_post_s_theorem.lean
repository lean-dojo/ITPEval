-- Canonical Lean registration for Thousand Theorems artifact Q3007384,
-- "Post's theorem". The statement is copied exactly from
-- the imported `ComputablePred.computable_iff_re_compl_re`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Computability.RE

@[expose] public section

namespace ThousandTheorems.Q3007384

/-- The Mathlib statement selected as the canonical Lean form of Post's theorem. -/
theorem canonical_statement : type_of% @ComputablePred.computable_iff_re_compl_re :=
  @ComputablePred.computable_iff_re_compl_re

end ThousandTheorems.Q3007384
