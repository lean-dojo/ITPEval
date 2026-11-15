-- Statement-only formalization of Thousand Theorems artifact Q1033910
-- (thousand-theorems__lean4__Q1033910), "Cantor–Bernstein–Schroeder theorem":
-- injections between arbitrary types in both directions imply the existence of a bijection.
-- This file contains no proof.

universe u v

namespace Function.Embedding

/-- The Cantor–Bernstein–Schroeder theorem for arbitrary types. -/
theorem schroeder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Injective h ∧ Function.Surjective h := sorry

end Function.Embedding
