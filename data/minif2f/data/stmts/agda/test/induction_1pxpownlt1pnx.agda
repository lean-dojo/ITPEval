-- Statement-only formalization of miniF2F test problem induction_1pxpownlt1pnx:
-- Bernoulli's inequality 1 + n*x <= (1 + x)^n for real x > -1 and positive
-- natural n, using a fixed Cauchy representation of the real numbers.
-- This file contains no proof.

module induction_1pxpownlt1pnx where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _∧_

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

PositiveNat : Nat → Set
PositiveNat n = NatLess zero n

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

ratNegativeOne : Rational
ratNegativeOne =
  fraction (signed zero (suc zero)) zero

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

RealExpression : Set
RealExpression = Nat → Rational

Cauchy : RealExpression → Set
Cauchy sequence =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (m n : Nat) →
    NatLe threshold m →
    NatLe threshold n →
    Close (sequence m) (sequence n) epsilon

-- Every standard real number has a rational Cauchy representative; all
-- relations below are invariant under eventual Cauchy equivalence.
record Real : Set where
  constructor cauchyReal
  field
    approximation : RealExpression
    isCauchy      : Cauchy approximation

constantExpression : Rational → RealExpression
constantExpression q index = q

leftExpression : Real → Nat → RealExpression
leftExpression x n index =
  ratAdd ratOne
    (ratMultiply
      (ratFromNat n)
      (Real.approximation x index))

ratPower : Rational → Nat → Rational
ratPower x zero = ratOne
ratPower x (suc n) =
  ratMultiply x (ratPower x n)

rightExpression : Real → Nat → RealExpression
rightExpression x n index =
  ratPower
    (ratAdd ratOne (Real.approximation x index))
    n

-- This is the usual non-strict order of the limits: every positive rational
-- tolerance eventually puts the first sequence below the second plus it.
SequenceLessOrEqual : RealExpression → RealExpression → Set
SequenceLessOrEqual firstSequence secondSequence =
  (epsilon : Rational) →
  Positive epsilon →
  Exists Nat λ threshold →
    (index : Nat) →
    NatLe threshold index →
    RationalLess
      (firstSequence index)
      (ratAdd (secondSequence index) epsilon)

-- A positive rational gap eventually separating the limits is equivalent to
-- strict order on the represented real numbers.
SequenceStrictLess : RealExpression → RealExpression → Set
SequenceStrictLess firstSequence secondSequence =
  Exists Rational λ gap →
    Positive gap ∧
    Exists Nat λ threshold →
      (index : Nat) →
      NatLe threshold index →
      RationalLess
        (ratAdd (firstSequence index) gap)
        (secondSequence index)

induction_1pxpownlt1pnx : Set
induction_1pxpownlt1pnx =
  (x : Real) →
  (n : Nat) →
  SequenceStrictLess
    (constantExpression ratNegativeOne)
    (Real.approximation x) →
  PositiveNat n →
  SequenceLessOrEqual
    (leftExpression x n)
    (rightExpression x n)
