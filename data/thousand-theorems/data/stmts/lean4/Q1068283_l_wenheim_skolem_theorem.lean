-- Statement-only formalization of Thousand Theorems artifact Q1068283
-- (thousand-theorems__lean4__Q1068283), "Löwenheim–Skolem theorem": for an infinite
-- first-order structure and a sufficiently large infinite cardinal, there is a structure
-- of that cardinality with an elementary embedding in one direction. This file contains no proof.

module

public import Mathlib.ModelTheory.Bundled
public import Mathlib.ModelTheory.Skolem
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder.Language

namespace Q1068283

/-- The Löwenheim–Skolem theorem for an infinite first-order structure. -/
theorem exists_elementaryEmbedding_card_eq (L : Language.{u, v}) (M : Type w')
    [L.Structure M] [Infinite M] (κ : Cardinal.{w}) (h1 : ℵ₀ ≤ κ)
    (h2 : lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : Bundled L.Structure,
      (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #N = κ := sorry

end Q1068283

end FirstOrder.Language
