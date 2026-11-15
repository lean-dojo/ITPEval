-- Statement-only formalization of thousand-theorems corpus artifact Q609612
-- (thousand-theorems__agda__Q609612), "Knaster–Tarski theorem": the fixed
-- points of a monotone self-map of a complete lattice form a complete lattice
-- under the inherited order. This file contains no proof.

{-# OPTIONS --safe --prop #-}

module Q609612_knaster_tarski_theorem where

open import Agda.Primitive using (Level; lsuc; Prop)

infix 4 _≡_

data _≡_
  {ℓ : Level}
  {A : Set ℓ}
  (x : A) :
  A → Prop ℓ where

  reflexivity :
    x ≡ x

record CompleteLattice
  {ℓ : Level}
  (A : Set ℓ) :
  Set (lsuc ℓ) where

  field
    lessOrEqual :
      A → A → Prop ℓ

    order-reflexive :
      (x : A) →
      lessOrEqual x x
    order-transitive :
      (x y z : A) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : A) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y

    supremum :
      (A → Prop ℓ) → A
    supremum-upper :
      (subset : A → Prop ℓ) →
      (x : A) →
      subset x →
      lessOrEqual x (supremum subset)
    supremum-least :
      (subset : A → Prop ℓ) →
      (upper : A) →
      ((x : A) → subset x → lessOrEqual x upper) →
      lessOrEqual (supremum subset) upper

    infimum :
      (A → Prop ℓ) → A
    infimum-lower :
      (subset : A → Prop ℓ) →
      (x : A) →
      subset x →
      lessOrEqual (infimum subset) x
    infimum-greatest :
      (subset : A → Prop ℓ) →
      (lower : A) →
      ((x : A) → subset x → lessOrEqual lower x) →
      lessOrEqual lower (infimum subset)

open CompleteLattice

record OrderEndomorphism
  {ℓ : Level}
  {A : Set ℓ}
  (lattice : CompleteLattice A) :
  Set ℓ where

  field
    function :
      A → A
    monotone :
      (x y : A) →
      lessOrEqual lattice x y →
      lessOrEqual lattice (function x) (function y)

open OrderEndomorphism

IsFixedPoint :
  {ℓ : Level} →
  {A : Set ℓ} →
  {lattice : CompleteLattice A} →
  OrderEndomorphism lattice →
  A →
  Prop ℓ
IsFixedPoint endomorphism x =
  function endomorphism x ≡ x

record FixedPointSubset
  {ℓ : Level}
  {A : Set ℓ}
  (lattice : CompleteLattice A)
  (endomorphism : OrderEndomorphism lattice) :
  Set (lsuc ℓ) where

  field
    carrier :
      A → Prop ℓ
    member-is-fixed :
      (x : A) →
      carrier x →
      IsFixedPoint endomorphism x

open FixedPointSubset

record FixedPointsCompleteLattice
  {ℓ : Level}
  {A : Set ℓ}
  (lattice : CompleteLattice A)
  (endomorphism : OrderEndomorphism lattice) :
  Set (lsuc ℓ) where

  field
    fixedSupremum :
      FixedPointSubset lattice endomorphism →
      A
    fixedSupremum-is-fixed :
      (subset : FixedPointSubset lattice endomorphism) →
      IsFixedPoint endomorphism (fixedSupremum subset)
    fixedSupremum-upper :
      (subset : FixedPointSubset lattice endomorphism) →
      (x : A) →
      carrier subset x →
      lessOrEqual lattice x (fixedSupremum subset)
    fixedSupremum-least :
      (subset : FixedPointSubset lattice endomorphism) →
      (upper : A) →
      IsFixedPoint endomorphism upper →
      ((x : A) →
        carrier subset x →
        lessOrEqual lattice x upper) →
      lessOrEqual lattice (fixedSupremum subset) upper

    fixedInfimum :
      FixedPointSubset lattice endomorphism →
      A
    fixedInfimum-is-fixed :
      (subset : FixedPointSubset lattice endomorphism) →
      IsFixedPoint endomorphism (fixedInfimum subset)
    fixedInfimum-lower :
      (subset : FixedPointSubset lattice endomorphism) →
      (x : A) →
      carrier subset x →
      lessOrEqual lattice (fixedInfimum subset) x
    fixedInfimum-greatest :
      (subset : FixedPointSubset lattice endomorphism) →
      (lower : A) →
      IsFixedPoint endomorphism lower →
      ((x : A) →
        carrier subset x →
        lessOrEqual lattice lower x) →
      lessOrEqual lattice lower (fixedInfimum subset)

KnasterTarskiTheorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
KnasterTarskiTheorem ℓ =
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  (endomorphism : OrderEndomorphism lattice) →
  FixedPointsCompleteLattice lattice endomorphism
