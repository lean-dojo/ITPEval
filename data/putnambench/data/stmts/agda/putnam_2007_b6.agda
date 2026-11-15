-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_b6
-- (putnambench__agda__putnam_2007_b6): factorial-coin multiset counts satisfy
-- the stated two-sided asymptotic bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc exponent) =
  multiply reals
    (naturalPower reals x exponent)
    x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirstReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirstReal reals zero term =
  zeroR reals
sumFirstReal reals (suc n) term =
  add reals
    (sumFirstReal reals n term)
    (term n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirstReal reals n terms)
    limit

exponentialTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals
    (exponentialTerm reals x)
    value

record StandardExpLog
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm :
      R ->
      R

    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

    logarithm-inverse :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (logarithm x) == x

open StandardExpLog

realPower :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExpLog reals ->
  R ->
  R ->
  R
realPower reals analysis base exponent =
  exponential analysis
    (multiply reals
      (logarithm analysis base)
      exponent)

sumFirstNat :
  Nat ->
  (Nat -> Nat) ->
  Nat
sumFirstNat zero term =
  zero
sumFirstNat (suc n) term =
  sumFirstNat n term + term n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN + twoN

CoinMultiset :
  Nat ->
  (Nat -> Nat) ->
  Set
CoinMultiset n multiplicity =
  Exists Nat
    (\ supportBound ->
      ((value : Nat) ->
        supportBound <=N value ->
        multiplicity value == zero)
      and
      sumFirstNat supportBound
        (\ value ->
          multiplicity value * value)
        == factorial n
      and
      ((value : Nat) ->
        oneN <=N multiplicity value ->
        Exists Nat
          (\ k ->
            oneN <=N k
            and
            k <=N n
            and
            value == factorial k)))

MultisetEqual :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
MultisetEqual leftMultiplicity rightMultiplicity =
  (value : Nat) ->
  leftMultiplicity value == rightMultiplicity value

record HasExtensionalCardinality
  {A : Set}
  (P : A -> Set)
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (item : A) ->
      P item ->
      Exists (Fin cardinality)
        (\ index ->
          equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent
        (enumerate left-index)
        (enumerate right-index) ->
      left-index == right-index

CountsFactorialCoinMultisets :
  (Nat -> Nat) ->
  Set
CountsFactorialCoinMultisets f =
  (n : Nat) ->
  HasExtensionalCardinality
    (CoinMultiset n)
    MultisetEqual
    (f n)

squareOfNat :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
squareOfNat reals n =
  multiply reals
    (fromNat reals n)
    (fromNat reals n)

halfSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
halfSquare reals n =
  divide reals
    (squareOfNat reals n)
    (fromNat reals twoN)

linearTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
linearTerm reals C n =
  multiply reals C (fromNat reals n)

lowerExponent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
lowerExponent reals C n =
  subtract reals
    (halfSquare reals n)
    (linearTerm reals C n)

upperExponent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
upperExponent reals C n =
  add reals
    (halfSquare reals n)
    (linearTerm reals C n)

negativeQuarterSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
negativeQuarterSquare reals n =
  negate reals
    (divide reals
      (squareOfNat reals n)
      (fromNat reals fourN))

scaledPower :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExpLog reals) ->
  Nat ->
  R ->
  R
scaledPower reals analysis n exponent =
  multiply reals
    (realPower reals analysis
      (fromNat reals n)
      exponent)
    (exponential analysis
      (negativeQuarterSquare reals n))

AsymptoticBounds :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExpLog reals ->
  (Nat -> Nat) ->
  Set
AsymptoticBounds {R} reals analysis f =
  Exists R
    (\ C ->
      (n : Nat) ->
      twoN <=N n ->
      lessOrEqual reals
        (scaledPower reals analysis n
          (lowerExponent reals C n))
        (fromNat reals (f n))
      and
      lessOrEqual reals
        (fromNat reals (f n))
        (scaledPower reals analysis n
          (upperExponent reals C n)))

putnam-2007-b6 : Set1
putnam-2007-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExpLog reals) ->
  (f : Nat -> Nat) ->
  CountsFactorialCoinMultisets f ->
  AsymptoticBounds reals analysis f
