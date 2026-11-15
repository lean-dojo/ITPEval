-- Statement-only formalization of miniF2F test problem mathd_algebra_33: for nonzero real x,
-- the proportionalities 2x = 5y and 7y = 10z force z/x = 7/25. Reals are represented by
-- regular rational Cauchy sequences modulo equality of limits, and the quotient conclusion is
-- encoded equivalently as 25z = 7x. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-33 where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _≤E_ _≈E_ _≉E_
infixr 4 _∧_
infixl 6 _+N_ _+Z_ _+Q_ _+E_
infixl 7 _*N_ _*Z_ _*Q_ _*E_

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

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

_*N_ : Nat → Nat → Nat
zero *N n = zero
suc m *N n = n +N (m *N n)

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤  : {m n : Nat} → m ≤N n → suc m ≤N suc n

-- Integers are differences of natural numbers.
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

RealExpression : Set
RealExpression = Nat → Rational

constant : Rational → RealExpression
constant q n = q

naturalExpression : Nat → RealExpression
naturalExpression n =
  constant (naturalRational n)

_+E_ : RealExpression → RealExpression → RealExpression
(x +E y) n = x n +Q y n

_*E_ : RealExpression → RealExpression → RealExpression
(x *E y) n = x n *Q y n

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Every represented real has a rational Cauchy presentation with this regular modulus.
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

-- These eventual relations are order and equality of the represented real limits.
_≤E_ : RealExpression → RealExpression → Set
x ≤E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    x index ≤Q (y index +Q unitFraction precision)

_≈E_ : RealExpression → RealExpression → Set
x ≈E y = (x ≤E y) ∧ (y ≤E x)

_≉E_ : RealExpression → RealExpression → Set
x ≉E y = x ≈E y → ⊥

scale : Nat → Real → RealExpression
scale n x =
  naturalExpression n *E realExpression x

mathd-algebra-33 : Set
mathd-algebra-33 =
  (x y z : Real) →
  realExpression x ≉E naturalExpression 0 →
  scale 2 x ≈E scale 5 y →
  scale 7 y ≈E scale 10 z →
  scale 25 z ≈E scale 7 x
