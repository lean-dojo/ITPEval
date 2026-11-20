theorem or_of_right (p q : Prop) (hq : q) : p ∨ q := by
  exact Or.inr hq

#print axioms or_of_right
