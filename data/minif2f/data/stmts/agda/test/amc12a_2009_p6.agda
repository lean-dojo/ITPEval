-- Statement-only formalization of miniF2F test problem amc12a_2009_p6: an identity for
-- real powers with bases 2, 3, and 12. This file contains no proof.

module amc12a-2009-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _∧_
infix 4 _≈ℝ_

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

-- A signed natural pair (positive part, negative part) represents their integer difference.
record SignedNat : Set where
  constructor signed
  field
    positivePart : Nat
    negativePart : Nat

signedAdd : SignedNat → SignedNat → SignedNat
signedAdd (signed a b) (signed c d) = signed (a + c) (b + d)

signedMultiply : SignedNat → SignedNat → SignedNat
signedMultiply (signed a b) (signed c d) =
  signed (a * c + b * d) (a * d + b * c)

signedScale : SignedNat → Nat → SignedNat
signedScale (signed a b) n = signed (a * n) (b * n)

SignedLess : SignedNat → SignedNat → Set
SignedLess (signed a b) (signed c d) = NatLess (a + d) (c + b)

-- A rational is a signed numerator over one plus denominatorMinusOne.
record Rational : Set where
  constructor fraction
  field
    numerator            : SignedNat
    denominatorMinusOne : Nat

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

ratZero : Rational
ratZero = fraction (signed zero zero) zero

ratOne : Rational
ratOne = fraction (signed (suc zero) zero) zero

ratFromNat : Nat → Rational
ratFromNat n = fraction (signed n zero) zero

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
Positive epsilon = RationalLess ratZero epsilon

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

EventuallyEquivalent : (Nat → Rational) → (Nat → Rational) → Set
EventuallyEquivalent first second =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (n : Nat) →
    NatLe threshold n →
    Close (first n) (second n) epsilon

-- Real numbers are concrete rational Cauchy sequences; _≈ℝ_ is equality in their quotient.
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

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

ratPower : Rational → Nat → Rational
ratPower x zero = ratOne
ratPower x (suc n) = ratMultiply x (ratPower x n)

expPartial : Nat → Rational → Rational
expPartial zero x = ratOne
expPartial (suc n) x =
  ratAdd
    (expPartial n x)
    (ratDivideNat
      (ratPower x (suc n))
      (factorial (suc n)))

-- Exponential x y means y = exp(x), using the rational Taylor series on Cauchy reals.
Exponential : Real → Real → Set
Exponential x y =
  EventuallyEquivalent
    (Real.approximation y)
    (λ n → expPartial n (Real.approximation x n))

-- For a positive base, base^exponent is exp(exponent * log(base)).
RealPower : Real → Real → Real → Set
RealPower base exponent result =
  Exists Real λ logarithm →
  Exists Real λ scaled →
    Exponential logarithm base ∧
    Multiply exponent logarithm scaled ∧
    Exponential scaled result

NatMultiply : Nat → Real → Real → Set
NatMultiply n x product =
  Exists Real λ constant →
    Constant n constant ∧
    Multiply constant x product

NatPower : Nat → Real → Real → Set
NatPower n exponent result =
  Exists Real λ base →
    Constant n base ∧
    RealPower base exponent result

amc12a-2009-p6 : Set
amc12a-2009-p6 =
  (m n p q : Real) →
  NatPower 2 m p →
  NatPower 3 n q →
  Exists Real λ two-times-n →
  Exists Real λ p-to-two-times-n →
  Exists Real λ q-to-m →
  Exists Real λ left-hand-side →
  Exists Real λ m-times-n →
  Exists Real λ right-hand-side →
    NatMultiply 2 n two-times-n ∧
    RealPower p two-times-n p-to-two-times-n ∧
    RealPower q m q-to-m ∧
    Multiply p-to-two-times-n q-to-m left-hand-side ∧
    Multiply m n m-times-n ∧
    NatPower 12 m-times-n right-hand-side ∧
    (left-hand-side ≈ℝ right-hand-side)
