-- Statement-only formalization of VERINA corpus artifact verina_basic_101,
-- catalog title "Triple": a deterministic integer program doubles its input,
-- adds the original input, and is connected to its integer-division
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic101 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_
infixl 7 _*z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

naturalDivThree : Nat → Nat
naturalDivThree zero = zero
naturalDivThree (suc zero) = zero
naturalDivThree (suc (suc zero)) = zero
naturalDivThree (suc (suc (suc n))) = suc (naturalDivThree n)

naturalCeilDivThree : Nat → Nat
naturalCeilDivThree zero = zero
naturalCeilDivThree (suc zero) = suc zero
naturalCeilDivThree (suc (suc zero)) = suc zero
naturalCeilDivThree (suc (suc (suc n))) =
  suc (naturalCeilDivThree n)

-- Lean integer division by the positive integer three rounds toward negative infinity.
divideByThree : Int → Int
divideByThree (pos n) = pos (naturalDivThree n)
divideByThree (negsuc n) =
  negative (naturalCeilDivThree (suc n))

Triple-precond : Int → Set
Triple-precond x = ⊤

Triple : (x : Int) → Triple-precond x → Int
Triple x h-precond =
  let y = x *z pos 2
  in y +z x

Triple-postcond : (x result : Int) → Triple-precond x → Set
Triple-postcond x result h-precond =
  (divideByThree result ≡ x) ∧
  ((divideByThree result *z pos 3) ≡ result)

Triple-spec-satisfied : Set
Triple-spec-satisfied =
  (x : Int) →
  (h-precond : Triple-precond x) →
  Triple-postcond x (Triple x h-precond) h-precond
