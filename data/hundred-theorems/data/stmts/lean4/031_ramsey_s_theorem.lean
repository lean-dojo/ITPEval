-- Statement-only formalization of "Ramsey's Theorem" from Hundred Theorems item 031. It
-- states that every finite coloring of fixed-size subsets of an infinite set has an infinite
-- homogeneous subset. This file contains no proof.

namespace Theorems100

universe u

abbrev Subset (α : Type u) := α → Prop

def IncludedIn {α : Type u} (s t : Subset α) : Prop :=
  ∀ x, s x → t x

def HasCardinality {α : Type u} (n : Nat) (s : Subset α) : Prop :=
  ∃ enumerate : Fin n → α,
    (∀ i, s (enumerate i)) ∧
      (∀ i j, enumerate i = enumerate j → i = j) ∧
        ∀ x, s x → ∃ i, enumerate i = x

def InfiniteSubset {α : Type u} (s : Subset α) : Prop :=
  ∀ n : Nat, ∃ choose : Fin n → α,
    (∀ i, s (choose i)) ∧
      ∀ i j, choose i = choose j → i = j

/--
Infinite Ramsey's theorem: if the `n`-element subsets of an infinite set receive only finitely
many colors, there is an infinite subset on which the coloring is constant.
-/
theorem ramsey_theorem {α : Type u} (n colors : Nat) (s : Subset α)
    (hs : InfiniteSubset s) (color : Subset α → Nat)
    (color_extensional :
      ∀ u v : Subset α, (∀ x, u x ↔ v x) → color u = color v)
    (color_bounded :
      ∀ u : Subset α, IncludedIn u s → HasCardinality n u → color u < colors) :
    ∃ t : Subset α, IncludedIn t s ∧ InfiniteSubset t ∧
      ∃ c : Nat, c < colors ∧
        ∀ u : Subset α, IncludedIn u t → HasCardinality n u → color u = c := sorry

end Theorems100
