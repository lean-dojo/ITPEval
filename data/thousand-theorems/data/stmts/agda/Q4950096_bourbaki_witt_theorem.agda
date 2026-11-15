-- Statement-only formalization of thousand-theorems corpus artifact Q4950096
-- (thousand-theorems__agda__Q4950096), "Bourbaki–Witt theorem": every
-- inflationary endofunction on a nonempty chain-complete partial order has a
-- fixed point. This file contains no proof.

{-# OPTIONS --safe #-}

module Q4950096_bourbaki_witt_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → Either A B
  right : B → Either A B

record Nonempty
  {ℓ : Level}
  (A : Set ℓ) :
  Set ℓ where

  constructor inhabited
  field
    element : A

record PartialOrder
  {ℓ : Level}
  (A : Set ℓ) :
  Set (lsuc ℓ) where

  field
    lessOrEqual :
      A → A → Set ℓ

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

open PartialOrder

record NonemptyChain
  {ℓ : Level}
  {A : Set ℓ}
  (order : PartialOrder A) :
  Set (lsuc ℓ) where

  field
    carrier :
      A → Set ℓ
    carrier-nonempty :
      Σ A carrier
    comparable :
      (x y : A) →
      carrier x →
      carrier y →
      Either
        (lessOrEqual order x y)
        (lessOrEqual order y x)

open NonemptyChain

record ChainCompletePartialOrder
  {ℓ : Level}
  (A : Set ℓ) :
  Set (lsuc ℓ) where

  field
    partialOrder :
      PartialOrder A
    chainSupremum :
      NonemptyChain partialOrder → A
    lessOrEqual-chainSupremum :
      (chain : NonemptyChain partialOrder) →
      (x : A) →
      carrier chain x →
      lessOrEqual partialOrder x (chainSupremum chain)
    chainSupremum-least :
      (chain : NonemptyChain partialOrder) →
      (upper : A) →
      ((x : A) →
        carrier chain x →
        lessOrEqual partialOrder x upper) →
      lessOrEqual partialOrder (chainSupremum chain) upper

open ChainCompletePartialOrder

BourbakiWittTheorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
BourbakiWittTheorem ℓ =
  (A : Set ℓ) →
  (order : ChainCompletePartialOrder A) →
  Nonempty A →
  (function : A → A) →
  ((x : A) →
    lessOrEqual
      (partialOrder order)
      x
      (function x)) →
  Σ A
    (λ fixedPoint →
      function fixedPoint ≡ fixedPoint)
