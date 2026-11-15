-- Statement-only formalization of miniF2F valid artifact mathd_algebra_22:
-- the real logarithm of 5^4 divided by the real logarithm of 5^2 equals 2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-22 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _∧_
infix 4 _≈ℝ_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data NatLe : Nat → Nat → Set where
  zero-le :
    {n : Nat} → NatLe zero n
  successor-le :
    {m n : Nat} → NatLe m n → NatLe (suc m) (suc n)

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

-- A signed natural pair represents the difference of its components.
record SignedNat : Set where
  constructor signed
  field
    positivePart : Nat
    negativePart : Nat

signedAdd : SignedNat → SignedNat → SignedNat
signedAdd (signed a b) (signed c d) =
  signed (a + c) (b + d)

signedMultiply : SignedNat → SignedNat → SignedNat
signedMultiply (signed a b) (signed c d) =
  signed (a * c + b * d) (a * d + b * c)

signedScale : SignedNat → Nat → SignedNat
signedScale (signed a b) n =
  signed (a * n) (b * n)

SignedLess : SignedNat → SignedNat → Set
SignedLess (signed a b) (signed c d) =
  NatLess (a + d) (c + b)

-- A rational is a signed numerator divided by one plus denominatorMinusOne.
record Rational : Set where
  constructor fraction
  field
    numerator           : SignedNat
    denominatorMinusOne : Nat

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

ratZero : Rational
ratZero =
  fraction (signed zero zero) zero

ratOne : Rational
ratOne =
  fraction (signed (suc zero) zero) zero

ratFromNat : Nat → Rational
ratFromNat n =
  fraction (signed n zero) zero

ratAdd : Rational → Rational → Rational
ratAdd (fraction x d) (fraction y e) =
  fraction
    (signedAdd
      (signedScale x (suc e))
      (signedScale y (suc d)))
    (predecessor ((suc d) * (suc e)))

ratMultiply : Rational → Rational → Rational
ratMultiply (fraction x d) (fraction y e) =
  fraction
    (signedMultiply x y)
    (predecessor ((suc d) * (suc e)))

ratDivideNat : Rational → Nat → Rational
ratDivideNat (fraction x d) n =
  fraction x (predecessor ((suc d) * n))

RationalLess : Rational → Rational → Set
RationalLess (fraction x d) (fraction y e) =
  SignedLess
    (signedScale x (suc e))
    (signedScale y (suc d))

Positive : Rational → Set
Positive epsilon =
  RationalLess ratZero epsilon

Close : Rational → Rational → Rational → Set
Close x y epsilon =
  RationalLess x (ratAdd y epsilon) ∧
  RationalLess y (ratAdd x epsilon)

Cauchy : (Nat → Rational) → Set
Cauchy sequence =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (m n : Nat) →
    NatLe threshold m →
    NatLe threshold n →
    Close (sequence m) (sequence n) epsilon

EventuallyEquivalent :
  (Nat → Rational) →
  (Nat → Rational) →
  Set
EventuallyEquivalent first second =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (n : Nat) →
    NatLe threshold n →
    Close (first n) (second n) epsilon

-- Rational Cauchy sequences modulo _≈ℝ_ are the standard real numbers.
record Real : Set where
  constructor cauchyReal
  field
    approximation : Nat → Rational
    isCauchy      : Cauchy approximation

_≈ℝ_ : Real → Real → Set
x ≈ℝ y =
  EventuallyEquivalent
    (Real.approximation x)
    (Real.approximation y)

Constant : Nat → Real → Set
Constant n x =
  EventuallyEquivalent
    (Real.approximation x)
    (λ _ → ratFromNat n)

Multiply : Real → Real → Real → Set
Multiply x y product =
  EventuallyEquivalent
    (Real.approximation product)
    (λ n →
      ratMultiply
        (Real.approximation x n)
        (Real.approximation y n))

Nonzero : Real → Set
Nonzero x =
  (zeroValue : Real) →
  Constant zero zeroValue →
  x ≈ℝ zeroValue →
  ⊥

Divide : Real → Real → Real → Set
Divide numerator denominator quotient =
  Nonzero denominator ∧
  Multiply quotient denominator numerator

ratPower : Rational → Nat → Rational
ratPower x zero =
  ratOne
ratPower x (suc n) =
  ratMultiply x (ratPower x n)

NaturalPower : Real → Nat → Real → Set
NaturalPower x exponent result =
  EventuallyEquivalent
    (Real.approximation result)
    (λ n → ratPower (Real.approximation x n) exponent)

factorial : Nat → Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

expPartial : Nat → Rational → Rational
expPartial zero x =
  ratOne
expPartial (suc n) x =
  ratAdd
    (expPartial n x)
    (ratDivideNat
      (ratPower x (suc n))
      (factorial (suc n)))

-- This graph is the standard real exponential on Cauchy representatives.
Exponential : Real → Real → Set
Exponential exponent result =
  EventuallyEquivalent
    (Real.approximation result)
    (λ n → expPartial n (Real.approximation exponent n))

-- On positive arguments, logarithm is the inverse graph of real exponential.
Logarithm : Real → Real → Set
Logarithm argument result =
  Exponential result argument

LogBase : Real → Real → Real → Set
LogBase base argument result =
  Exists Real λ logarithmOfArgument →
  Exists Real λ logarithmOfBase →
    Logarithm argument logarithmOfArgument ∧
    Logarithm base logarithmOfBase ∧
    Divide logarithmOfArgument logarithmOfBase result

mathd-algebra-22 : Set
mathd-algebra-22 =
  Exists Real λ five →
  Exists Real λ base →
  Exists Real λ argument →
  Exists Real λ result →
    Constant 5 five ∧
    NaturalPower five 2 base ∧
    NaturalPower five 4 argument ∧
    LogBase base argument result ∧
    Constant 2 result
