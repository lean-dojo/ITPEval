-- Statement-only formalization of Logipedia corpus artifact
-- "leibniz.refl_leibniz" (catalog title "leibniz.refl_leibniz"): Leibniz
-- equality is reflexive for every element of every type. This file contains no proof.

namespace leibniz

def leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

theorem refl_leibniz :
    ∀ (A : Type) (x : A), leibniz A x x := sorry

end leibniz
