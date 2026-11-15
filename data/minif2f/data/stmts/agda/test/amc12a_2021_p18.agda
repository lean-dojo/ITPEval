-- Statement-only formalization of miniF2F test problem amc12a_2021_p18: a
-- positive-rational multiplicative-to-additive function normalized on primes
-- is negative at 25/11. This file contains no proof.

module amc12a-2021-p18 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _<Q_ _≈Q_ _≈E_ _<E_
infixr 3 _∧_
infixr 2 _∨_
infixl 6 _+N_ _+Z_ _+Q_ _+E_
infixl 7 _*N_ _*Z_ _*Q_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d *N quotient ≡ n

record Prime (n : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) ≤N n
    divisor-is-trivial :
      (d : Nat) →
      Divides d n →
      d ≡ suc zero ∨ d ≡ n

-- Integers are quotient representatives p - n. The order below identifies
-- representatives of the same integer.
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

-- A denominator is stored as one plus a natural number, so it is positive by
-- construction.
data PositiveDenominator : Set where
  onePlus : Nat → PositiveDenominator

denominatorValue : PositiveDenominator → Nat
denominatorValue (onePlus n) = suc n

_*D_ : PositiveDenominator → PositiveDenominator → PositiveDenominator
onePlus m *D onePlus n =
  onePlus ((m +N n) +N (m *N n))

record Rational : Set where
  constructor fraction
  field
    numerator   : Integer
    denominator : PositiveDenominator

scaleInteger : Integer → PositiveDenominator → Integer
scaleInteger z d =
  z *Z naturalInteger (denominatorValue d)

_+Q_ : Rational → Rational → Rational
fraction x xd +Q fraction y yd =
  fraction
    ((scaleInteger x yd) +Z (scaleInteger y xd))
    (xd *D yd)

negateQ : Rational → Rational
negateQ (fraction x xd) =
  fraction (negateZ x) xd

subtractQ : Rational → Rational → Rational
subtractQ x y = x +Q negateQ y

_*Q_ : Rational → Rational → Rational
fraction x xd *Q fraction y yd =
  fraction (x *Z y) (xd *D yd)

_≤Q_ : Rational → Rational → Set
fraction x xd ≤Q fraction y yd =
  scaleInteger x yd ≤Z scaleInteger y xd

_≈Q_ : Rational → Rational → Set
x ≈Q y = (x ≤Q y) ∧ (y ≤Q x)

_<Q_ : Rational → Rational → Set
x <Q y = (x ≤Q y) ∧ Not (y ≤Q x)

naturalRational : Nat → Rational
naturalRational n =
  fraction (naturalInteger n) (onePlus zero)

rationalZero : Rational
rationalZero = naturalRational zero

unitFraction : Nat → Rational
unitFraction n =
  fraction (naturalInteger (suc zero)) (onePlus n)

PositiveRational : Rational → Set
PositiveRational q = rationalZero <Q q

RealExpression : Set
RealExpression = Nat → Rational

constant : Rational → RealExpression
constant q n = q

naturalExpression : Nat → RealExpression
naturalExpression n =
  constant (naturalRational n)

_+E_ : RealExpression → RealExpression → RealExpression
(x +E y) n = x n +Q y n

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Every classical real has a rational approximation with this regular Cauchy
-- modulus, and two such approximations denote the same real exactly when they
-- become arbitrarily close.
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

_≈E_ : RealExpression → RealExpression → Set
x ≈E y =
  (precision : Nat) →
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    Close (x index) (y index) (unitFraction precision)

_<E_ : RealExpression → RealExpression → Set
x <E y =
  Exists Rational λ gap →
    PositiveRational gap ∧
    Exists Nat λ threshold →
      (index : Nat) →
      threshold ≤N index →
      (x index +Q gap) ≤Q y index

twentyFiveElevenths : Rational
twentyFiveElevenths =
  fraction (naturalInteger 25) (onePlus 10)

amc12a-2021-p18 : Set
amc12a-2021-p18 =
  (f : Rational → Real) →
  ((x y : Rational) →
    x ≈Q y →
    realExpression (f x) ≈E realExpression (f y)) →
  ((x y : Rational) →
    PositiveRational x →
    PositiveRational y →
    realExpression (f (x *Q y)) ≈E
    (realExpression (f x) +E realExpression (f y))) →
  ((p : Nat) →
    Prime p →
    realExpression (f (naturalRational p)) ≈E
    naturalExpression p) →
  realExpression (f twentyFiveElevenths) <E
  constant rationalZero
