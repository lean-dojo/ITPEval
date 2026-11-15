-- Statement-only formalization of VERINA corpus artifact verina_basic_99,
-- catalog title "Triple": a deterministic branched integer program computes
-- three times its input and is connected to its integer-division correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic99 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_
infixl 7 _*z_
infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

naturalDivTwo : Nat → Nat
naturalDivTwo zero = zero
naturalDivTwo (suc zero) = zero
naturalDivTwo (suc (suc n)) = suc (naturalDivTwo n)

naturalCeilDivTwo : Nat → Nat
naturalCeilDivTwo zero = zero
naturalCeilDivTwo (suc zero) = suc zero
naturalCeilDivTwo (suc (suc n)) =
  suc (naturalCeilDivTwo n)

-- Lean integer division by positive two rounds toward negative infinity.
divideByTwo : Int → Int
divideByTwo (pos n) = pos (naturalDivTwo n)
divideByTwo (negsuc n) =
  negative (naturalCeilDivTwo (suc n))

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
  if intLess x (pos 18)
  then
    (let a = pos 2 *z x
         b = pos 4 *z x
     in divideByTwo (a +z b))
  else
    (let y = pos 2 *z x
     in x +z y)

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
