-- Statement-only formalization of VERINA corpus artifact verina_basic_98,
-- catalog title "Triple": a deterministic integer program multiplies its
-- input by three and is connected to its integer-division correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic98 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 7 _*z_
infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

naturalDivThree : Nat → Nat
naturalDivThree zero = zero
naturalDivThree (suc zero) = zero
naturalDivThree (suc (suc zero)) = zero
naturalDivThree (suc (suc (suc n))) =
  suc (naturalDivThree n)

naturalCeilDivThree : Nat → Nat
naturalCeilDivThree zero = zero
naturalCeilDivThree (suc zero) = suc zero
naturalCeilDivThree (suc (suc zero)) = suc zero
naturalCeilDivThree (suc (suc (suc n))) =
  suc (naturalCeilDivThree n)

-- Lean integer division by positive three rounds toward negative infinity.
divideByThree : Int → Int
divideByThree (pos n) = pos (naturalDivThree n)
divideByThree (negsuc n) =
  negative (naturalCeilDivThree (suc n))

Triple-precond : Int → Set
Triple-precond x = Top

Triple :
  (x : Int) →
  Triple-precond x →
  Int
Triple x h-precond =
  x *z pos 3

Triple-postcond :
  (x result : Int) →
  Triple-precond x →
  Set
Triple-postcond x result h-precond =
  (divideByThree result ≡ x) ∧
  ((divideByThree result *z pos 3) ≡ result)

Triple-spec-satisfied : Set
Triple-spec-satisfied =
  (x : Int) →
  (h-precond : Triple-precond x) →
  Triple-postcond
    x
    (Triple x h-precond)
    h-precond
