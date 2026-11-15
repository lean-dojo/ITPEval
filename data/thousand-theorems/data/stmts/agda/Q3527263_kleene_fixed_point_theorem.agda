-- Statement-only formalization of thousand-theorems corpus artifact Q3527263
-- (thousand-theorems__agda__Q3527263), "Kleene fixed-point theorem": the
-- least fixed point of an omega-Scott-continuous order endomorphism of a
-- complete lattice is the supremum of its finite iterates from bottom.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527263_kleene_fixed_point_theorem where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

data Bottom {ℓ : Level} : Set ℓ where

data NatLessOrEqual : Nat → Nat → Set where
  zero-less-or-equal :
    {n : Nat} →
    NatLessOrEqual zero n
  successors-less-or-equal :
    {m n : Nat} →
    NatLessOrEqual m n →
    NatLessOrEqual (suc m) (suc n)

record CompleteLattice
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

    supremum :
      (A → Set ℓ) → A
    supremum-upper :
      (P : A → Set ℓ) →
      (x : A) →
      P x →
      lessOrEqual x (supremum P)
    supremum-least :
      (P : A → Set ℓ) →
      (upper : A) →
      ((x : A) → P x → lessOrEqual x upper) →
      lessOrEqual (supremum P) upper

    infimum :
      (A → Set ℓ) → A
    infimum-lower :
      (P : A → Set ℓ) →
      (x : A) →
      P x →
      lessOrEqual (infimum P) x
    infimum-greatest :
      (P : A → Set ℓ) →
      (lower : A) →
      ((x : A) → P x → lessOrEqual lower x) →
      lessOrEqual lower (infimum P)

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

record Chain
  {ℓ : Level}
  {A : Set ℓ}
  (lattice : CompleteLattice A) :
  Set ℓ where

  field
    value :
      Nat → A
    increasing :
      (m n : Nat) →
      NatLessOrEqual m n →
      lessOrEqual lattice (value m) (value n)

open Chain

chainSupremum :
  {ℓ : Level} →
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  Chain lattice →
  A
chainSupremum lattice chain =
  supremum lattice
    (λ x → Σ Nat (λ n → x ≡ value chain n))

OmegaScottContinuous :
  {ℓ : Level} →
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  OrderEndomorphism lattice →
  Set ℓ
OmegaScottContinuous lattice endomorphism =
  (chain : Chain lattice) →
  function endomorphism (chainSupremum lattice chain) ≡
  supremum lattice
    (λ y →
      Σ Nat
        (λ n → y ≡ function endomorphism (value chain n)))

bottom :
  {ℓ : Level} →
  {A : Set ℓ} →
  CompleteLattice A →
  A
bottom lattice =
  supremum lattice (λ _ → Bottom)

iterate :
  {ℓ : Level} →
  {A : Set ℓ} →
  (A → A) →
  Nat →
  A →
  A
iterate f zero x =
  x
iterate f (suc n) x =
  f (iterate f n x)

leastFixedPoint :
  {ℓ : Level} →
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  OrderEndomorphism lattice →
  A
leastFixedPoint lattice endomorphism =
  infimum lattice
    (λ x →
      lessOrEqual lattice (function endomorphism x) x)

iteratesSupremum :
  {ℓ : Level} →
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  OrderEndomorphism lattice →
  A
iteratesSupremum lattice endomorphism =
  supremum lattice
    (λ x →
      Σ Nat
        (λ n →
          x ≡
          iterate
            (function endomorphism)
            n
            (bottom lattice)))

KleeneFixedPointTheorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
KleeneFixedPointTheorem ℓ =
  {A : Set ℓ} →
  (lattice : CompleteLattice A) →
  (endomorphism : OrderEndomorphism lattice) →
  OmegaScottContinuous lattice endomorphism →
  leastFixedPoint lattice endomorphism ≡
  iteratesSupremum lattice endomorphism
