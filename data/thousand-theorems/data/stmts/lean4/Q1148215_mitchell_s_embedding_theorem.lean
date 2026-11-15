-- Statement-only formalization of Thousand Theorems artifact Q1148215
-- (thousand-theorems__lean4__Q1148215), "Mitchell's embedding theorem":
-- every abelian category admits a full and faithful embedding into modules over
-- a ring that preserves finite limits and finite colimits. This file contains no proof.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

universe v u

open CategoryTheory Limits

namespace Q1148215

/-- The Freyd-Mitchell embedding theorem for an arbitrary abelian category. -/
theorem mitchell_embedding_theorem_statement (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := sorry

end Q1148215
