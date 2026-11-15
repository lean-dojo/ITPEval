-- Statement-only formalization of thousand-theorems corpus artifact Q1033910
-- (thousand-theorems__agda__Q1033910), "Cantor–Bernstein–Schroeder theorem":
-- injections between two arbitrary types in both directions imply the existence
-- of a bijection. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1033910_cantor_bernstein_schroeder_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

Injective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) →
  function x ≡ function y →
  x ≡ y

Surjective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Surjective {A = A} {B = B} function =
  (y : B) →
  Σ A (λ x → function x ≡ y)

Bijective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Bijective function =
  Injective function × Surjective function

cantor-bernstein-schroeder-theorem :
  {a b : Level} →
  Set (lsuc (a ⊔ b))
cantor-bernstein-schroeder-theorem {a} {b} =
  (A : Set a) →
  (B : Set b) →
  (f : A → B) →
  (g : B → A) →
  Injective f →
  Injective g →
  Σ (A → B) (λ h → Bijective h)
