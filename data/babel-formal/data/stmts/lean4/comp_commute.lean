universe u v w

namespace CompCommute

variable {α : Type u} {β : Type v} {γ : Type w}

def comp {α β γ} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
def id {α} : α → α := fun x => x

axiom comp_assoc : ∀ {α β γ δ} (h : γ → δ) (g : β → γ) (f : α → β), comp h (comp g f) = comp (comp h g) f
axiom comp_id_l  : ∀ {α β} (f : α → β), comp (id) f = f
axiom comp_id_r  : ∀ {α β} (f : α → β), comp f id = f

def commute {α} (f g : α → α) : Prop := comp f g = comp g f

theorem commute_symm {α} (f g : α → α) : commute f g → commute g f := by sorry
theorem commute_with_id_l {α} (f : α → α) : commute f (id) := by sorry
theorem commute_with_id_r {α} (f : α → α) : commute (id) f := by sorry
theorem commute_refl {α} (f : α → α) : commute f f := by sorry
theorem commute_congr {α} (f1 f2 g1 g2 : α → α) :
  f1 = f2 → g1 = g2 → commute f1 g1 → commute f2 g2 := by sorry
theorem commute_transport_left_id {α} (f g : α → α) :
  commute f g → commute (comp (id) f) g := by sorry
theorem commute_transport_right_id {α} (f g : α → α) :
  commute f g → commute f (comp (id) g) := by sorry
end CompCommute
