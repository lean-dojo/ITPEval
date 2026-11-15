/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Zorn

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, Injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the folder `SetTheory.Cardinal`.
-/

public section


open Set Function

universe u v

namespace Function

namespace Embedding

section antisymm

variable {α : Type u} {β : Type v}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α` that satisfy a pointwise property `R`, we can get a bijection
`α → β` that satisfies that same pointwise property. -/
theorem schroeder_bernstein_of_rel {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) (R : α → β → Prop) (hp₁ : ∀ a : α, R a (f a))
    (hp₂ : ∀ b : β, R (g b) b) :
    ∃ h : α → β, Bijective h ∧ ∀ a : α, R a (h a) := by sorry
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : α → β, Bijective h := by sorry
theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β) := by sorry
end antisymm

section Wo

variable {ι : Type u} (β : ι → Type v)

/-- `sets β` -/
private abbrev sets :=
  { s : Set (∀ i, β i) | ∀ i : ι, s.InjOn fun x => x i }

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others.
See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice instances. -/
theorem min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs⟩ := show ∃ s, Maximal (· ∈ sets β) s by
    refine zorn_subset _ fun c hc hcc ↦
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi ↦ ?_, fun _ ↦ subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h ↦ hc hqc i (h hxp) hyq hi)
      fun h ↦ hc hpc i hxp (h hyq) hi
  let ⟨i, e⟩ :=
    show ∃ i, Surjective fun x : s => x.val i from
      Classical.by_contradiction fun h =>
        have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y := by sorry
end Wo

/-- The cardinals are totally ordered. See
`Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice
instance. -/
theorem total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (ULift α) (ULift.{max u v, v} β)) ⟨true⟩
    with := by sorry
end Embedding

end Function
