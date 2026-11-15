universe u

class LatticeLike (A : Type u) where
  le   : A → A → Prop
  inf  : A → A → A
  sup  : A → A → A

  le_refl  : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisym : ∀ {x y}, le x y → le y x → x = y

  le_inf_left  : ∀ a b, le (inf a b) a
  le_inf_right : ∀ a b, le (inf a b) b
  le_inf_intro : ∀ {c a b}, le c a → le c b → le c (inf a b)

  le_sup_left  : ∀ a b, le a (sup a b)
  le_sup_right : ∀ a b, le b (sup a b)
  sup_le_intro : ∀ {a b c}, le a c → le b c → le (sup a b) c

namespace LatticeLike

variable {A : Type u} [L : LatticeLike A]

infix:50 " ≤ " => LatticeLike.le
infixl:65 " ⊓ " => LatticeLike.inf
infixl:70 " ⊔ " => LatticeLike.sup

theorem inf_comm (a b : A) : a ⊓ b = b ⊓ a := by sorry
theorem sup_comm (a b : A) : a ⊔ b = b ⊔ a := by sorry
theorem inf_assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) := by sorry
theorem sup_assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by sorry
theorem inf_absorption (a b : A) : a ⊓ (a ⊔ b) = a := by sorry
theorem sup_absorption (a b : A) : a ⊔ (a ⊓ b) = a := by sorry
end LatticeLike
