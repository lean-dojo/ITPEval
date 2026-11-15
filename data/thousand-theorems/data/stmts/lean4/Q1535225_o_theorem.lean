-- Statement-only formalization of Thousand Theorems artifact Q1535225
-- (thousand-theorems__lean4__Q1535225), "Łoś' theorem": a first-order sentence
-- holds in an ultraproduct if and only if it holds in almost every factor with
-- respect to the ultrafilter. This file contains no proof.

module

public import Mathlib.ModelTheory.Ultraproducts

@[expose] public section

universe u v

open FirstOrder Filter

namespace FirstOrder.Language

open Structure

namespace Q1535225

/-- Łoś's theorem for first-order sentences in an ultraproduct. -/
theorem sentence_realize {α : Type*} {L : Language.{u, v}} {M : α → Type*}
    {𝒰 : Ultrafilter α} [∀ a, L.Structure (M a)] [∀ a, Nonempty (M a)]
    (φ : L.Sentence) :
    (𝒰 : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in 𝒰, M a ⊨ φ := sorry

end Q1535225

end FirstOrder.Language
