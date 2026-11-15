-- Statement-only formalization of miniF2F valid problem amc12a_2010_p22:
-- every real x gives a 119-term sum of |k * x - 1| that is at least 49.
-- This file contains no proof.

module amc12a-2010-p22 where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _≤E_
infixr 4 _∧_
infixl 6 _+N_ _∸N_ _+Z_ _+Q_ _+E_ _-E_
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

_∸N_ : Nat → Nat → Nat
n ∸N zero = n
zero ∸N suc n = zero
suc m ∸N suc n = m ∸N n

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤  : {m n : Nat} → m ≤N n → suc m ≤N suc n

-- Integers are quotient-aware differences of natural numbers.
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

absoluteZ : Integer → Integer
absoluteZ (integer p n) =
  integer ((p ∸N n) +N (n ∸N p)) zero

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

absoluteQ : Rational → Rational
absoluteQ (fraction x xd) =
  fraction (absoluteZ x) xd

_≤Q_ : Rational → Rational → Set
fraction x xd ≤Q fraction y yd =
  scaleInteger x yd ≤Z scaleInteger y xd

naturalRational : Nat → Rational
naturalRational n =
  fraction (naturalInteger n) (onePlus zero)

unitFraction : Nat → Rational
unitFraction n =
  fraction (naturalInteger (suc zero)) (onePlus n)

RealExpression : Set
RealExpression = Nat → Rational

constant : Rational → RealExpression
constant q n = q

naturalExpression : Nat → RealExpression
naturalExpression n =
  constant (naturalRational n)

_+E_ : RealExpression → RealExpression → RealExpression
(x +E y) n = x n +Q y n

negateE : RealExpression → RealExpression
negateE x n = negateQ (x n)

_-E_ : RealExpression → RealExpression → RealExpression
x -E y = x +E negateE y

_*E_ : RealExpression → RealExpression → RealExpression
(x *E y) n = x n *Q y n

absoluteE : RealExpression → RealExpression
absoluteE x n = absoluteQ (x n)

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Every standard real has rational approximations with this fixed regularity
-- modulus; different approximations denote the same real through eventual
-- arbitrarily close comparison.
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

realExpression : Real → RealExpression
realExpression = Real.approximation

-- On regular rational presentations, this is exactly the usual order of
-- their real limits and is invariant under replacement by an equivalent
-- Cauchy presentation.
_≤E_ : RealExpression → RealExpression → Set
x ≤E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    x index ≤Q (y index +Q unitFraction precision)

summand : RealExpression → Nat → RealExpression
summand x k =
  absoluteE
    ((naturalExpression k *E x) -E naturalExpression 1)

sumFromOne : RealExpression → Nat → RealExpression
sumFromOne x zero =
  naturalExpression zero
sumFromOne x (suc n) =
  sumFromOne x n +E summand x (suc n)

amc12a-2010-p22 : Set
amc12a-2010-p22 =
  (x : Real) →
  naturalExpression 49 ≤E
  sumFromOne (realExpression x) 119
