universe u

namespace SetAlgebra

variable {X : Type u}

axiom classic : ∀ P : Prop, P ∨ ¬ P

def sUnion (A B : X → Prop) : X → Prop := fun x => A x ∨ B x
def sInter (A B : X → Prop) : X → Prop := fun x => A x ∧ B x
def sCompl (A : X → Prop) : X → Prop := fun x => ¬ A x

infixl:65  " ∪s " => sUnion
infixl:70  " ∩s " => sInter
prefix:100 "ᶜs" => sCompl

theorem inter_distrib_left (A B C : X → Prop) :
  ∀ x, (A ∩s (B ∪s C)) x ↔ ((A ∩s B) ∪s (A ∩s C)) x := by sorry
theorem inter_distrib_right (A B C : X → Prop) :
  ∀ x, ((A ∪s B) ∩s C) x ↔ ((A ∩s C) ∪s (B ∩s C)) x := by sorry
theorem de_morgan_union (A B : X → Prop) :
  ∀ x, (ᶜs (A ∪s B)) x ↔ (ᶜs A ∩s ᶜs B) x := by sorry
theorem de_morgan_inter (A B : X → Prop) :
  ∀ x, (ᶜs (A ∩s B)) x ↔ (ᶜs A ∪s ᶜs B) x := by sorry
end SetAlgebra
