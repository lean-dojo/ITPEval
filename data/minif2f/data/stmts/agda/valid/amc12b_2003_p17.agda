-- Statement-only formalization of miniF2F valid problem amc12b_2003_p17 using standard
-- reals as rational Cauchy sequences modulo eventual equivalence: positive x and y with
-- ln(x * y^3) = 1 and ln(x^2 * y) = 1 satisfy ln(x * y) = 3/5.
-- This file contains no proof.

module amc12b-2003-p17 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _∧_
infix 4 _≈ℝ_

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    first  : A
    second : B

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

-- A signed natural pair represents the difference of its two components.
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
ratZero =
  fraction (signed zero zero) zero

ratOne : Rational
ratOne =
  fraction (signed (suc zero) zero) zero

ratThreeFifths : Rational
ratThreeFifths =
  fraction
    (signed (suc (suc (suc zero))) zero)
    (suc (suc (suc (suc zero))))

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
EventuallyEquivalent firstSequence secondSequence =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (n : Nat) →
    NatLe threshold n →
    Close (firstSequence n) (secondSequence n) epsilon

-- A Real is a Cauchy representative. EventuallyEquivalent is equality in the
-- quotient; every operation below is defined only through that equality.
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

Constant : Rational → Real → Set
Constant q x =
  EventuallyEquivalent
    (Real.approximation x)
    (λ _ → q)

-- General Cauchy sequences are closed under pointwise multiplication. Giving
-- the result as a Real witness makes that closure internal to the graph.
Multiply : Real → Real → Real → Set
Multiply x y product =
  EventuallyEquivalent
    (Real.approximation product)
    (λ n →
      ratMultiply
        (Real.approximation x n)
        (Real.approximation y n))

ratPower : Rational → Nat → Rational
ratPower x zero = ratOne
ratPower x (suc n) =
  ratMultiply x (ratPower x n)

-- NaturalPower is likewise a total, representative-invariant graph on the
-- Cauchy quotient rather than a raw fixed-modulus sequence operation.
NaturalPower : Real → Nat → Real → Set
NaturalPower x exponent result =
  EventuallyEquivalent
    (Real.approximation result)
    (λ n → ratPower (Real.approximation x n) exponent)

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) =
  suc n * factorial n

expPartial : Nat → Rational → Rational
expPartial zero x = ratOne
expPartial (suc n) x =
  ratAdd
    (expPartial n x)
    (ratDivideNat
      (ratPower x (suc n))
      (factorial (suc n)))

-- The diagonal Taylor sequence converges to the standard real exponential.
-- Its graph is stated modulo eventual equivalence, so changing either Cauchy
-- representative does not change the represented proposition.
Exponential : Real → Real → Set
Exponential exponent result =
  EventuallyEquivalent
    (Real.approximation result)
    (λ n →
      expPartial n (Real.approximation exponent n))

-- On positive arguments this inverse graph is exactly the standard natural
-- logarithm. Real arguments and values already carry Cauchy membership, so
-- this definition adds no regularity condition on a chosen representative.
Logarithm : Real → Real → Set
Logarithm argument value =
  Exponential value argument

PositiveReal : Real → Set
PositiveReal x =
  Exists Rational λ gap →
    Positive gap ∧
    Exists Nat λ threshold →
      (n : Nat) →
      NatLe threshold n →
      RationalLess gap (Real.approximation x n)

FirstLogEquation : Real → Real → Set
FirstLogEquation x y =
  Exists Real λ yCubed →
  Exists Real λ product →
  Exists Real λ one →
    NaturalPower y 3 yCubed ∧
    Multiply x yCubed product ∧
    Constant ratOne one ∧
    Logarithm product one

SecondLogEquation : Real → Real → Set
SecondLogEquation x y =
  Exists Real λ xSquared →
  Exists Real λ product →
  Exists Real λ one →
    NaturalPower x 2 xSquared ∧
    Multiply xSquared y product ∧
    Constant ratOne one ∧
    Logarithm product one

ProductLogEqualsThreeFifths : Real → Real → Set
ProductLogEqualsThreeFifths x y =
  Exists Real λ product →
  Exists Real λ threeFifths →
    Multiply x y product ∧
    Constant ratThreeFifths threeFifths ∧
    Logarithm product threeFifths

amc12b-2003-p17 : Set
amc12b-2003-p17 =
  (x y : Real) →
  PositiveReal x →
  PositiveReal y →
  FirstLogEquation x y →
  SecondLogEquation x y →
  ProductLogEqualsThreeFifths x y
