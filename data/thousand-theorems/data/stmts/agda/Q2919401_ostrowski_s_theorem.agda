-- Statement-only formalization of thousand-theorems corpus artifact Q2919401,
-- "Ostrowski's theorem": every nontrivial real-valued absolute value on the
-- rationals is equivalent either to the usual absolute value or uniquely to
-- a p-adic absolute value for a prime p. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2919401_ostrowski_s_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper; mod-helper)

infix 4 _!=_ _<=N_ _divides_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  field
    unique-value    : A
    unique-property : P unique-value
    uniqueness      : (other : A) -> P other -> other == unique-value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record Prime (p : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == suc zero) or (d == p)

natPred : Nat -> Nat
natPred zero =
  zero
natPred (suc n) =
  n

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  suc zero
naturalPower base (suc exponent) =
  base * naturalPower base exponent

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natLessOrEqualBool : Nat -> Nat -> Bool
natLessOrEqualBool zero n =
  true
natLessOrEqualBool (suc m) zero =
  false
natLessOrEqualBool (suc m) (suc n) =
  natLessOrEqualBool m n

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

intNegate : Int -> Int
intNegate (pos n) =
  negativeNat n
intNegate (negsuc n) =
  pos (suc n)

intDifference : Nat -> Nat -> Int
intDifference zero zero =
  pos zero
intDifference (suc m) zero =
  pos (suc m)
intDifference zero (suc n) =
  negsuc n
intDifference (suc m) (suc n) =
  intDifference m n

intAdd : Int -> Int -> Int
intAdd (pos m) (pos n) =
  pos (m + n)
intAdd (pos m) (negsuc n) =
  intDifference m (suc n)
intAdd (negsuc m) (pos n) =
  intDifference n (suc m)
intAdd (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

intMultiply : Int -> Int -> Int
intMultiply (pos m) (pos n) =
  pos (m * n)
intMultiply (pos m) (negsuc n) =
  negativeNat (m * suc n)
intMultiply (negsuc m) (pos n) =
  negativeNat (suc m * n)
intMultiply (negsuc m) (negsuc n) =
  pos (suc m * suc n)

intAbsolute : Int -> Nat
intAbsolute (pos n) =
  n
intAbsolute (negsuc n) =
  suc n

data IntLessOrEqual : Int -> Int -> Set where
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    IntLessOrEqual (pos m) (pos n)
  negative<=positive :
    {m n : Nat} ->
    IntLessOrEqual (negsuc m) (pos n)
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    IntLessOrEqual (negsuc m) (negsuc n)

record Rational : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

rationalZero : Rational
rationalZero =
  fraction (pos zero) zero

rationalOne : Rational
rationalOne =
  fraction (pos (suc zero)) zero

rationalFromNat : Nat -> Rational
rationalFromNat n =
  fraction (pos n) zero

rationalNegate : Rational -> Rational
rationalNegate q =
  fraction
    (intNegate (numerator q))
    (denominator-minus-one q)

rationalAdd : Rational -> Rational -> Rational
rationalAdd x y =
  fraction
    (intAdd
      (intMultiply (numerator x) (pos (denominator y)))
      (intMultiply (numerator y) (pos (denominator x))))
    (natPred (denominator x * denominator y))

rationalSubtract : Rational -> Rational -> Rational
rationalSubtract x y =
  rationalAdd x (rationalNegate y)

rationalMultiply : Rational -> Rational -> Rational
rationalMultiply x y =
  fraction
    (intMultiply (numerator x) (numerator y))
    (natPred (denominator x * denominator y))

rationalPower : Rational -> Nat -> Rational
rationalPower base zero =
  rationalOne
rationalPower base (suc exponent) =
  rationalMultiply base (rationalPower base exponent)

rationalDivideByPositiveNat : Rational -> Nat -> Rational
rationalDivideByPositiveNat q divisor =
  fraction
    (numerator q)
    (natPred (denominator q * divisor))

rationalUnitFraction : Nat -> Rational
rationalUnitFraction denominator-minus-one =
  fraction (pos (suc zero)) denominator-minus-one

rationalAbsolute : Rational -> Rational
rationalAbsolute q =
  fraction
    (pos (intAbsolute (numerator q)))
    (denominator-minus-one q)

RationalEqual : Rational -> Rational -> Set
RationalEqual x y =
  intMultiply (numerator x) (pos (denominator y)) ==
  intMultiply (numerator y) (pos (denominator x))

RationalLessOrEqual : Rational -> Rational -> Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (intMultiply (numerator x) (pos (denominator y)))
    (intMultiply (numerator y) (pos (denominator x)))

RationalDistance : Rational -> Rational -> Rational
RationalDistance x y =
  rationalAbsolute (rationalSubtract x y)

Real : Set
Real =
  Nat -> Rational

constantReal : Rational -> Real
constantReal q n =
  q

realZero : Real
realZero =
  constantReal rationalZero

realOne : Real
realOne =
  constantReal rationalOne

realNegate : Real -> Real
realNegate x n =
  rationalNegate (x n)

realAdd : Real -> Real -> Real
realAdd x y n =
  rationalAdd (x n) (y n)

realMultiply : Real -> Real -> Real
realMultiply x y n =
  rationalMultiply (x n) (y n)

RealCauchy : Real -> Set
RealCauchy x =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      RationalLessOrEqual
        (RationalDistance (x m) (x n))
        (rationalUnitFraction precision))

RealEqual : Real -> Real -> Set
RealEqual x y =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      RationalLessOrEqual
        (RationalDistance (x n) (y n))
        (rationalUnitFraction precision))

RealLess : Real -> Real -> Set
RealLess x y =
  Exists Nat
    (\ precision ->
      Exists Nat
        (\ cutoff ->
          (n : Nat) ->
          cutoff <=N n ->
          RationalLessOrEqual
            (rationalAdd (x n) (rationalUnitFraction precision))
            (y n)))

RealLessOrEqual : Real -> Real -> Set
RealLessOrEqual x y =
  Not (RealLess y x)

exponentialPartialSum : Rational -> Nat -> Rational
exponentialPartialSum point zero =
  rationalOne
exponentialPartialSum point (suc n) =
  rationalAdd
    (exponentialPartialSum point n)
    (rationalDivideByPositiveNat
      (rationalPower point (suc n))
      (factorial (suc n)))

exponentialSequence : Real -> Real
exponentialSequence x n =
  exponentialPartialSum (x n) n

RealExponential : Real -> Real -> Set
RealExponential x result =
  RealCauchy x
  and
  RealCauchy (exponentialSequence x)
  and
  RealCauchy result
  and
  RealEqual result (exponentialSequence x)

RealLogarithm : Real -> Real -> Set
RealLogarithm base logarithm =
  RealLess realZero base
  and
  RealExponential logarithm base

RealRpow : Real -> Real -> Real -> Set
RealRpow base exponent result =
  RealCauchy base
  and
  RealCauchy exponent
  and
  RealCauchy result
  and
  (((RealEqual base realZero)
    and
    (RealLess realZero exponent)
    and
    (RealEqual result realZero))
  or
  ((RealLess realZero base)
    and
    Exists Real
      (\ logarithm ->
        RealLogarithm base logarithm
        and
        RealExponential
          (realMultiply exponent logarithm)
          result)))

valuationBound : Nat -> Nat -> Nat -> Nat
valuationBound p zero fuel =
  zero
valuationBound p (suc n) zero =
  zero
valuationBound p (suc n) (suc fuel) with naturalMod (suc n) p
... | zero =
  suc (valuationBound p (naturalDiv (suc n) p) fuel)
... | suc remainder =
  zero

padicValuationNat : Nat -> Nat -> Nat
padicValuationNat p n =
  valuationBound p n n

padicMagnitudeFromValuations : Nat -> Nat -> Nat -> Rational
padicMagnitudeFromValuations p numerator-valuation denominator-valuation
  with natLessOrEqualBool numerator-valuation denominator-valuation
... | true =
  rationalFromNat
    (naturalPower p (denominator-valuation - numerator-valuation))
... | false =
  rationalUnitFraction
    (natPred
      (naturalPower p (numerator-valuation - denominator-valuation)))

padicMagnitude : Nat -> Rational -> Rational
padicMagnitude p q with numerator q
... | pos zero =
  rationalZero
... | pos (suc n) =
  padicMagnitudeFromValuations p
    (padicValuationNat p (suc n))
    (padicValuationNat p (denominator q))
... | negsuc n =
  padicMagnitudeFromValuations p
    (padicValuationNat p (suc n))
    (padicValuationNat p (denominator q))

standardAbsoluteValue : Rational -> Real
standardAbsoluteValue q =
  constantReal (rationalAbsolute q)

padicAbsoluteValue : Nat -> Rational -> Real
padicAbsoluteValue p q =
  constantReal (padicMagnitude p q)

record AbsoluteValue : Set where
  field
    apply : Rational -> Real
    value-is-real :
      (x : Rational) ->
      RealCauchy (apply x)
    respects-rational-equality :
      (x y : Rational) ->
      RationalEqual x y ->
      RealEqual (apply x) (apply y)
    nonnegative :
      (x : Rational) ->
      RealLessOrEqual realZero (apply x)
    zero-exactly :
      (x : Rational) ->
      Iff
        (RealEqual (apply x) realZero)
        (RationalEqual x rationalZero)
    map-multiply :
      (x y : Rational) ->
      RealEqual
        (apply (rationalMultiply x y))
        (realMultiply (apply x) (apply y))
    triangle-inequality :
      (x y : Rational) ->
      RealLessOrEqual
        (apply (rationalAdd x y))
        (realAdd (apply x) (apply y))

open AbsoluteValue

IsNontrivial : AbsoluteValue -> Set
IsNontrivial absolute-value =
  Exists Rational
    (\ x ->
      Not (RationalEqual x rationalZero)
      and
      Not (RealEqual (apply absolute-value x) realOne))

PositiveReal : Real -> Set
PositiveReal x =
  RealCauchy x
  and
  RealLess realZero x

EquivalentToStandard : AbsoluteValue -> Set
EquivalentToStandard absolute-value =
  Exists Real
    (\ exponent ->
      PositiveReal exponent
      and
      ((x : Rational) ->
        RealRpow
          (apply absolute-value x)
          exponent
          (standardAbsoluteValue x)))

EquivalentToPadic : AbsoluteValue -> Nat -> Set
EquivalentToPadic absolute-value p =
  Exists Real
    (\ exponent ->
      PositiveReal exponent
      and
      ((x : Rational) ->
        RealRpow
          (apply absolute-value x)
          exponent
          (padicAbsoluteValue p x)))

ostrowski-theorem : Set
ostrowski-theorem =
  (absolute-value : AbsoluteValue) ->
  IsNontrivial absolute-value ->
  EquivalentToStandard absolute-value
  or
  ExistsUnique Nat
    (\ p ->
      Prime p
      and
      EquivalentToPadic absolute-value p)
