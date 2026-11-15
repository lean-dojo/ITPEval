-- Statement-only formalization of Logipedia corpus artifact
-- "leibniz.sym_leibniz" (catalog title "leibniz.sym_leibniz"): Leibniz
-- equality is symmetric for every pair of elements of every type.
-- This file contains no proof.

namespace leibniz

def leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

theorem sym_leibniz :
    ∀ (A : Type) (x y : A), leibniz A x y → leibniz A y x := sorry

end leibniz
