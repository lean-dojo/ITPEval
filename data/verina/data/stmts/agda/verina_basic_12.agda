-- Statement-only formalization of VERINA corpus artifact verina_basic_12,
-- catalog title "cubeSurfaceArea": a deterministic natural-number program
-- computes six times the square of a cube's edge length and is connected to
-- its truncated-subtraction correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic12 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

six : Nat
six = suc (suc (suc (suc (suc (suc zero)))))

cubeSurfaceArea-precond : Nat → Set
cubeSurfaceArea-precond size = Top

cubeSurfaceArea :
  (size : Nat) →
  cubeSurfaceArea-precond size →
  Nat
cubeSurfaceArea size h-precond =
  (six * size) * size

cubeSurfaceArea-postcond :
  (size result : Nat) →
  cubeSurfaceArea-precond size →
  Set
cubeSurfaceArea-postcond size result h-precond =
  (natSubtract result ((six * size) * size) ≡ zero) ∧
  (natSubtract ((six * size) * size) result ≡ zero)

cubeSurfaceArea-spec-satisfied : Set
cubeSurfaceArea-spec-satisfied =
  (size : Nat) →
  (h-precond : cubeSurfaceArea-precond size) →
  cubeSurfaceArea-postcond
    size
    (cubeSurfaceArea size h-precond)
    h-precond
