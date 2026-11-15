-- Statement-only formalization of VERINA corpus artifact verina_basic_65,
-- catalog title "SquareRoot": a deterministic bounded natural-number loop
-- computes the integer square root and is connected to the contract that its
-- square is at most N while the next square exceeds N. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic65 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

SquareRoot-precond : Nat → Set
SquareRoot-precond N = Top

SquareRoot-boundedLoop : Nat → Nat → Nat → Nat
SquareRoot-boundedLoop N zero r = r
SquareRoot-boundedLoop N (suc bound) r =
  if natLessOrEqual ((suc r) * (suc r)) N
  then SquareRoot-boundedLoop N bound (suc r)
  else r

SquareRoot :
  (N : Nat) →
  SquareRoot-precond N →
  Nat
SquareRoot N h-precond =
  SquareRoot-boundedLoop N (suc N) zero

SquareRoot-postcond :
  (N result : Nat) →
  SquareRoot-precond N →
  Set
SquareRoot-postcond N result h-precond =
  (result * result ≤ N) ∧
  (N < (suc result) * (suc result))

SquareRoot-spec-satisfied : Set
SquareRoot-spec-satisfied =
  (N : Nat) →
  (h-precond : SquareRoot-precond N) →
  SquareRoot-postcond
    N
    (SquareRoot N h-precond)
    h-precond
