-- Statement-only formalization of Thousand Theorems artifact Q33481
-- (thousand-theorems__lean4__Q33481), "Arrow's impossibility theorem": every social
-- welfare function on at least three alternatives that satisfies weak Pareto and
-- independence of irrelevant alternatives is dictatorial. This file contains no proof.

module

public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Q33481

universe u v

/-- A preference order is a reflexive, total, transitive binary relation. -/
structure PreferenceOrder (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  total : ∀ x y, rel x y ∨ rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

instance {α : Type u} : CoeFun (PreferenceOrder α) (fun _ ↦ α → α → Prop) :=
  ⟨PreferenceOrder.rel⟩

/-- The strict part of a preference order. -/
def StrictPreference {α : Type u} (r : PreferenceOrder α) (x y : α) : Prop :=
  r x y ∧ ¬r y x

/-- Two preference orders rank a specified pair in the same strict way. -/
def SameStrictOrder {α : Type u} (r r' : PreferenceOrder α) (x y : α) : Prop :=
  (StrictPreference r x y ↔ StrictPreference r' x y) ∧
    (StrictPreference r y x ↔ StrictPreference r' y x)

/-- The weak Pareto condition on a finite set of alternatives. -/
def WeakPareto {α : Type u} {ι : Type v}
    (f : (ι → PreferenceOrder α) → PreferenceOrder α) (X : Finset α) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ R : ι → PreferenceOrder α,
    (∀ i : ι, StrictPreference (R i) x y) → StrictPreference (f R) x y

/-- Independence of irrelevant alternatives on a finite set of alternatives. -/
def IndependentOfIrrelevantAlternatives {α : Type u} {ι : Type v}
    (f : (ι → PreferenceOrder α) → PreferenceOrder α) (X : Finset α) : Prop :=
  ∀ R R' : ι → PreferenceOrder α, ∀ x ∈ X, ∀ y ∈ X,
    (∀ i : ι, SameStrictOrder (R i) (R' i) x y) →
      SameStrictOrder (f R) (f R') x y

/-- A social welfare function is dictatorial on a finite set of alternatives. -/
def IsDictatorship {α : Type u} {ι : Type v}
    (f : (ι → PreferenceOrder α) → PreferenceOrder α) (X : Finset α) : Prop :=
  ∃ i : ι, ∀ x ∈ X, ∀ y ∈ X, ∀ R : ι → PreferenceOrder α,
    StrictPreference (R i) x y → StrictPreference (f R) x y

/-- Arrow's impossibility theorem for a finite electorate and at least three alternatives. -/
theorem arrow_s_impossibility_theorem {α : Type u} {ι : Type v} [Fintype ι]
    {f : (ι → PreferenceOrder α) → PreferenceOrder α} {X : Finset α}
    (hwp : WeakPareto f X) (hiia : IndependentOfIrrelevantAlternatives f X)
    (hX : 3 ≤ X.card) : IsDictatorship f X := sorry

end Q33481
