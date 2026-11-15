-- Statement-only formalization of miniF2F test problem
-- algebra_ineq_nto1onlt2m1on using rational Cauchy sequences for the standard
-- real numbers: n^(1/n) <= 2 - 1/n for every natural n. This file contains no proof.

{-# OPTIONS --safe #-}

module algebra_ineq_nto1onlt2m1on where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _≤E_
infixr 4 _∧_
infixl 6 _+N_ _+Z_ _+Q_
infixl 7 _*N_ _*Z_ _*Q_ _*E_

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

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

_*N_ : Nat → Nat → Nat
zero *N n = zero
suc m *N n = n +N (m *N n)

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤  : {m n : Nat} → m ≤N n → suc m ≤N suc n

-- Integers are represented by differences of natural numbers.
record Integer : Set where
  constructor integer
  field
    positivePart : Nat
    negativePart : Nat

naturalInteger : Nat → Integer
naturalInteger n = integer n zero

_+Z_ : Integer → Integer → Integer
integer p n +Z integer q m =
  integer (p +N q) (n +N m)

negateZ : Integer → Integer
negateZ (integer p n) = integer n p

_*Z_ : Integer → Integer → Integer
integer p n *Z integer q m =
  integer
    ((p *N q) +N (n *N m))
    ((p *N m) +N (n *N q))

_≤Z_ : Integer → Integer → Set
integer p n ≤Z integer q m =
  (p +N m) ≤N (q +N n)

-- A positive denominator is stored as one plus a natural number.
data Positive : Set where
  onePlus : Nat → Positive

positiveValue : Positive → Nat
positiveValue (onePlus n) = suc n

_*P_ : Positive → Positive → Positive
onePlus m *P onePlus n =
  onePlus ((m +N n) +N (m *N n))

record Rational : Set where
  constructor fraction
  field
    numerator   : Integer
    denominator : Positive

scaleInteger : Integer → Positive → Integer
scaleInteger z d =
  z *Z naturalInteger (positiveValue d)

_+Q_ : Rational → Rational → Rational
fraction x xd +Q fraction y yd =
  fraction
    ((scaleInteger x yd) +Z (scaleInteger y xd))
    (xd *P yd)

negateQ : Rational → Rational
negateQ (fraction x xd) =
  fraction (negateZ x) xd

_*Q_ : Rational → Rational → Rational
fraction x xd *Q fraction y yd =
  fraction (x *Z y) (xd *P yd)

_≤Q_ : Rational → Rational → Set
fraction x xd ≤Q fraction y yd =
  scaleInteger x yd ≤Z scaleInteger y xd

naturalRational : Nat → Rational
naturalRational n =
  fraction (naturalInteger n) (onePlus zero)

unitFraction : Nat → Rational
unitFraction n =
  fraction (naturalInteger (suc zero)) (onePlus n)

-- Division by zero is totalized as zero, matching the source prover
-- conventions used in the unguarded natural-number statements.
reciprocalNatural : Nat → Rational
reciprocalNatural zero = naturalRational zero
reciprocalNatural (suc n) = unitFraction n

twoMinusReciprocal : Nat → Rational
twoMinusReciprocal n =
  naturalRational 2 +Q negateQ (reciprocalNatural n)

RealExpression : Set
RealExpression = Nat → Rational

constant : Rational → RealExpression
constant q index = q

naturalExpression : Nat → RealExpression
naturalExpression n =
  constant (naturalRational n)

_*E_ : RealExpression → RealExpression → RealExpression
(x *E y) index = x index *Q y index

powerE : RealExpression → Nat → RealExpression
powerE x zero = naturalExpression 1
powerE x (suc n) = x *E powerE x n

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Regular rational Cauchy sequences, modulo equality of limits, give the
-- fixed standard real-number domain rather than an arbitrary real structure.
Regular : RealExpression → Set
Regular x =
  (m n : Nat) →
  Close
    (x m)
    (x n)
    (unitFraction m +Q unitFraction n)

record Real : Set where
  constructor real
  field
    approximation : RealExpression
    regular       : Regular approximation

-- On regular rational presentations, this is the usual non-strict order of
-- their real limits.
_≤E_ : RealExpression → RealExpression → Set
x ≤E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    x index ≤Q (y index +Q unitFraction precision)

upperBound : Nat → RealExpression
upperBound n = constant (twoMinusReciprocal n)

-- For positive n and a nonnegative upper bound u,
-- n^(1/n) <= u iff n <= u^n.  The zero branch records the totalized source
-- value 0^(1/0) = 0^0 = 1.
reciprocalPowerLessOrEqual : Nat → RealExpression → Set
reciprocalPowerLessOrEqual zero u =
  naturalExpression 1 ≤E u
reciprocalPowerLessOrEqual (suc n) u =
  (naturalExpression 0 ≤E u) ∧
  (naturalExpression (suc n) ≤E powerE u (suc n))

algebra_ineq_nto1onlt2m1on : Set
algebra_ineq_nto1onlt2m1on =
  (n : Nat) →
  reciprocalPowerLessOrEqual n (upperBound n)
