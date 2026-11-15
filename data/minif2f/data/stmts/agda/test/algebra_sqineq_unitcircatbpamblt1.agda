-- Statement-only formalization of miniF2F test problem
-- algebra_sqineq_unitcircatbpamblt1: a unit-circle quadratic inequality
-- for two real numbers. This file contains no proof.

module algebra_sqineq_unitcircatbpamblt1 where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _≈E_ _≤E_
infixr 4 _∧_
infixl 6 _+N_ _+Z_ _+Q_ _+E_ _-E_
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

-- Integers are exact differences of natural numbers.
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

squareE : RealExpression → RealExpression
squareE x = x *E x

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Every real number has a rational presentation with this regular modulus.
Regular : RealExpression → Set
Regular x =
  (m n : Nat) →
  Close
    (x m)
    (x n)
    (unitFraction m +Q unitFraction n)

-- Real values are regular rational Cauchy presentations; equivalent
-- presentations denote the same element of the Cauchy completion.
record Real : Set where
  constructor real
  field
    approximation : RealExpression
    regular       : Regular approximation

realExpression : Real → RealExpression
realExpression = Real.approximation

_≈E_ : RealExpression → RealExpression → Set
x ≈E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    Close (x index) (y index) (unitFraction precision)

_≤E_ : RealExpression → RealExpression → Set
x ≤E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    x index ≤Q (y index +Q unitFraction precision)

algebra_sqineq_unitcircatbpamblt1 : Set
algebra_sqineq_unitcircatbpamblt1 =
  (a b : Real) →
  (squareE (realExpression a) +E squareE (realExpression b))
    ≈E naturalExpression 1 →
  ((realExpression a *E realExpression b) +E
    (realExpression a -E realExpression b))
    ≤E naturalExpression 1
