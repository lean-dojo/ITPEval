-- Statement-only formalization of VERINA corpus artifact verina_basic_107,
-- catalog title "ComputeAvg": a deterministic integer program computes the
-- floor-rounded average of two integers, with its exact quotient-remainder
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic107 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixl 6 _+z_ _-z_
infixl 7 _*z_

record Top : Set where
  constructor top

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

_-z_ : Int → Int → Int
x -z y = x +z negateInt y

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

naturalModTwo : Nat → Nat
naturalModTwo zero = zero
naturalModTwo (suc zero) = suc zero
naturalModTwo (suc (suc n)) = naturalModTwo n

-- Lean integer division by positive two rounds toward negative infinity.
divideByTwo : Int → Int
divideByTwo (pos n) = pos (naturalDivTwo n)
divideByTwo (negsuc n) =
  negative (naturalCeilDivTwo (suc n))

-- Lean remainder modulo positive two is the nonnegative parity remainder.
moduloByTwo : Int → Int
moduloByTwo (pos n) = pos (naturalModTwo n)
moduloByTwo (negsuc n) = pos (naturalModTwo (suc n))

ComputeAvg-precond : Int → Int → Set
ComputeAvg-precond a b = Top

ComputeAvg :
  (a b : Int) →
  ComputeAvg-precond a b →
  Int
ComputeAvg a b h-precond =
  divideByTwo (a +z b)

ComputeAvg-postcond :
  (a b result : Int) →
  ComputeAvg-precond a b →
  Set
ComputeAvg-postcond a b result h-precond =
  (pos 2 *z result) ≡
  ((a +z b) -z moduloByTwo (a +z b))

ComputeAvg-spec-satisfied : Set
ComputeAvg-spec-satisfied =
  (a b : Int) →
  (h-precond : ComputeAvg-precond a b) →
  ComputeAvg-postcond
    a
    b
    (ComputeAvg a b h-precond)
    h-precond
