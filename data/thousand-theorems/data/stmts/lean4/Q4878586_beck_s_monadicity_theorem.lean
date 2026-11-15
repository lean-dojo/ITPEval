-- Statement-only formalization of Thousand Theorems artifact Q4878586
-- (thousand-theorems__lean4__Q4878586), "Beck's monadicity theorem": a right
-- adjoint G that creates coequalizers of G-split pairs is monadic.
-- This file contains no proof.

module

public import Mathlib.CategoryTheory.Monad.Monadicity

@[expose] public section

universe v₁ u₁ u₂

namespace CategoryTheory.Monad.Q4878586

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D}

/-- Beck's monadicity theorem for a right adjoint creating its split coequalizers. -/
noncomputable def monadic_of_creates_G_split_coequalizers_statement
    (adj : F ⊣ G) [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := sorry

end CategoryTheory.Monad.Q4878586
