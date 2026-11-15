-- Statement-only formalization of VERINA corpus artifact verina_basic_48,
-- catalog title "isPerfectSquare": a deterministic fuel-bounded search decides
-- whether a natural number is a perfect square and is connected to its
-- Boolean-existential correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic48 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 2 _↔_

record Top : Set where
  constructor top

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

one : Nat
one = suc zero

isPerfectSquare-precond : Nat → Set
isPerfectSquare-precond n = Top

isPerfectSquare-check : Nat → Nat → Nat → Bool
isPerfectSquare-check n x zero = false
isPerfectSquare-check n x (suc fuel) =
  if natLess n (x * x)
  then false
  else
    if natEqual (x * x) n
    then true
    else isPerfectSquare-check n (suc x) fuel

isPerfectSquare : Nat → Bool
isPerfectSquare n =
  if natEqual n zero
  then true
  else isPerfectSquare-check n one n

isPerfectSquare-postcond : Nat → Bool → Set
isPerfectSquare-postcond n result =
  IsTrue result ↔
  Exists (λ i → i * i ≡ n)

isPerfectSquare-spec-satisfied : Set
isPerfectSquare-spec-satisfied =
  (n : Nat) →
  isPerfectSquare-postcond n (isPerfectSquare n)
