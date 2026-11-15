-- Statement-only formalization of VERINA corpus artifact verina_basic_55,
-- catalog title "Compare": deterministic equality comparison of two integers
-- returns the corresponding Boolean and satisfies both result branches.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic55 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

Compare-precond : Int → Int → Set
Compare-precond a b = Top

Compare :
  (a b : Int) →
  Compare-precond a b →
  Bool
Compare a b h-precond = intEqual a b

Compare-postcond :
  (a b : Int) →
  (result : Bool) →
  Compare-precond a b →
  Set
Compare-postcond a b result h-precond =
  ((a ≡ b) → (result ≡ true)) ∧
  (Not (a ≡ b) → (result ≡ false))

Compare-spec-satisfied : Set
Compare-spec-satisfied =
  (a b : Int) →
  (h-precond : Compare-precond a b) →
  Compare-postcond
    a
    b
    (Compare a b h-precond)
    h-precond
