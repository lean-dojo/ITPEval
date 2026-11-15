-- Statement-only formalization of miniF2F valid problem amc12a_2003_p24 using the standard
-- real numbers as regular rational Cauchy sequences: zero is the greatest value of the sum of
-- two change-of-base logarithmic ratios when 1 < b and b <= a. This file contains no proof.

module amc12a-2003-p24 where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤N_ _≤Z_ _≤Q_ _≈E_ _≤E_ _<E_
infixr 4 _∧_
infixl 6 _+N_ _+Z_ _+Q_ _+E_
infixl 7 _*N_ _*Z_ _*Q_ _*E_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

-- Integers are differences of natural numbers; the relations below quotient
-- the noncanonical representatives by cross addition.
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

zeroE : RealExpression
zeroE = constant (naturalRational zero)

oneE : RealExpression
oneE = constant (naturalRational (suc zero))

_+E_ : RealExpression → RealExpression → RealExpression
(x +E y) n = x n +Q y n

negateE : RealExpression → RealExpression
negateE x n = negateQ (x n)

_-E_ : RealExpression → RealExpression → RealExpression
x -E y = x +E negateE y

_*E_ : RealExpression → RealExpression → RealExpression
(x *E y) n = x n *Q y n

Close : Rational → Rational → Rational → Set
Close x y tolerance =
  (x ≤Q (y +Q tolerance)) ∧
  (y ≤Q (x +Q tolerance))

-- Every standard real has a representative with this fixed Cauchy modulus.
Regular : RealExpression → Set
Regular x =
  (m n : Nat) →
  Close
    (x m)
    (x n)
    (unitFraction m +Q unitFraction n)

-- Regular expressions modulo this relation are exactly the Cauchy real
-- numbers. All arithmetic and order below are invariant under it.
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

-- A positive rational gap characterizes strict order on Cauchy reals.
_<E_ : RealExpression → RealExpression → Set
x <E y =
  Exists Nat λ gap →
    Exists Nat λ threshold →
      (index : Nat) →
      threshold ≤N index →
      (x index +Q unitFraction gap) ≤Q y index

powerE : RealExpression → Nat → RealExpression
powerE x zero = oneE
powerE x (suc n) = powerE x n *E x

factorialDenominator : Nat → Positive
factorialDenominator zero = onePlus zero
factorialDenominator (suc n) =
  onePlus n *P factorialDenominator n

reciprocalFactorial : Nat → Rational
reciprocalFactorial n =
  fraction
    (naturalInteger (suc zero))
    (factorialDenominator n)

sumFirst :
  (Nat → RealExpression) →
  Nat →
  RealExpression
sumFirst term zero = zeroE
sumFirst term (suc n) =
  sumFirst term n +E term n

exponentialPartialSum :
  RealExpression →
  Nat →
  RealExpression
exponentialPartialSum x n =
  sumFirst
    (λ k → constant (reciprocalFactorial k) *E powerE x k)
    n

WithinPrecision :
  RealExpression →
  RealExpression →
  Nat →
  Set
WithinPrecision x y precision =
  Exists Nat λ threshold →
    (index : Nat) →
    threshold ≤N index →
    Close (x index) (y index) (unitFraction precision)

SequentialLimit :
  (Nat → RealExpression) →
  RealExpression →
  Set
SequentialLimit sequence limit =
  (precision : Nat) →
  Exists Nat λ cutoff →
    (n : Nat) →
    cutoff ≤N n →
    WithinPrecision (sequence n) limit precision

-- This is the standard real exponential, characterized by its everywhere
-- convergent Taylor series. Its inverse relation on positive reals is ln.
record Exponential
  (exponent result : RealExpression) : Set where
  field
    exponent-real : Regular exponent
    result-real   : Regular result
    series-limit  :
      SequentialLimit
        (exponentialPartialSum exponent)
        result

Logarithm :
  RealExpression →
  RealExpression →
  Set
Logarithm argument value =
  Exponential value argument

-- On the nonzero denominators used below, this relational form is exactly
-- ordinary real division and keeps every quotient witness internally scoped.
record Quotient
  (numerator denominator quotient : RealExpression) : Set where
  field
    numerator-real   : Regular numerator
    denominator-real : Regular denominator
    quotient-real    : Regular quotient
    quotient-equation :
      (quotient *E denominator) ≈E numerator

record ObjectiveValue
  (a b y : RealExpression) : Set where
  field
    a-over-b b-over-a : RealExpression
    log-a log-b : RealExpression
    log-a-over-b log-b-over-a : RealExpression
    first-term second-term : RealExpression

    divide-a-by-b :
      Quotient a b a-over-b
    divide-b-by-a :
      Quotient b a b-over-a

    logarithm-a :
      Logarithm a log-a
    logarithm-b :
      Logarithm b log-b
    logarithm-a-over-b :
      Logarithm a-over-b log-a-over-b
    logarithm-b-over-a :
      Logarithm b-over-a log-b-over-a

    first-change-of-base-ratio :
      Quotient log-a-over-b log-a first-term
    second-change-of-base-ratio :
      Quotient log-b-over-a log-b second-term

    value-equation :
      y ≈E (first-term +E second-term)

record GeneratedValue (y : RealExpression) : Set where
  field
    value-real : Regular y
    a b : RealExpression
    a-real : Regular a
    b-real : Regular b
    one-less-than-b : oneE <E b
    b-less-or-equal-a : b ≤E a
    objective-value : ObjectiveValue a b y

IsGreatest :
  (RealExpression → Set) →
  RealExpression →
  Set
IsGreatest predicate greatest =
  predicate greatest ∧
  ((y : RealExpression) →
    predicate y →
    y ≤E greatest)

amc12a-2003-p24 : Set
amc12a-2003-p24 =
  IsGreatest GeneratedValue zeroE
