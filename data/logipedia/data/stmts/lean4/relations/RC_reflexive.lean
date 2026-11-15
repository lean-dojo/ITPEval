-- Statement-only formalization of Logipedia corpus artifact
-- "relations.RC_reflexive" (catalog title "relations.RC_reflexive"): the reflexive
-- closure of every binary relation is reflexive. This file contains no proof.

namespace relations

def reflexive (A : Type) (R : A → A → Prop) : Prop :=
  ∀ x : A, R x x

def RC (A : Type) (R : A → A → Prop) (x y : A) : Prop :=
  R x y ∨ x = y

theorem RC_reflexive :
    ∀ (A : Type) (R : A → A → Prop), reflexive A (RC A R) := sorry

end relations
