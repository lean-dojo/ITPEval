-- Statement-only formalization of Thousand Theorems corpus artifact Q4116459
-- (thousand-theorems__agda__Q4116459), "Niven's theorem": a rational multiple
-- of pi with rational cosine has cosine equal to -1, -1/2, 0, 1/2, or 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q4116459_niven_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zeroR :
      inverseR zeroR == zeroR
    multiply-inverseR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    absolute-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) ==
      addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) ==
      multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedField

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (inverseR reals y)

fromIntR :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromIntR reals (pos n) =
  fromNatR reals n
fromIntR reals (negsuc n) =
  negateR reals (fromNatR reals (suc n))

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (absoluteR reals (subtractR reals x center))
    radius

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  addR reals
    (sumFirst reals n terms)
    (terms n)

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiplyR reals
    (naturalPower reals x n)
    x

alternate :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R ->
  R
alternate reals zero x =
  x
alternate reals (suc n) x =
  negateR reals (alternate reals n x)

evenExponent : Nat -> Nat
evenExponent n =
  n + n

oddExponent : Nat -> Nat
oddExponent n =
  suc (evenExponent n)

sineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  alternate reals n
    (divideR reals
      (naturalPower reals x (oddExponent n))
      (fromNatR reals (factorial (oddExponent n))))

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  alternate reals n
    (divideR reals
      (naturalPower reals x (evenExponent n))
      (fromNatR reals (factorial (evenExponent n))))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    value

record StandardTrigonometry
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    sine cosine : R -> R
    pi : R

    sine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)
    cosine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi
    sine-pi-zero :
      sine pi == zeroR reals
    pi-is-first-positive-sine-zero :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      sine x == zeroR reals ->
      lessOrEqualR reals pi x

open StandardTrigonometry

rationalValue :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  Nat ->
  R
rationalValue reals numerator denominatorMinusOne =
  divideR reals
    (fromIntR reals numerator)
    (fromNatR reals (suc denominatorMinusOne))

RationalReal :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
RationalReal reals x =
  Exists Int
    (\ numerator ->
      Exists Nat
        (\ denominatorMinusOne ->
          x ==
          rationalValue reals numerator denominatorMinusOne))

RationalMultipleOfPi :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardTrigonometry reals ->
  R ->
  Set
RationalMultipleOfPi reals trigonometry theta =
  Exists Int
    (\ numerator ->
      Exists Nat
        (\ denominatorMinusOne ->
          theta ==
          multiplyR reals
            (rationalValue reals numerator denominatorMinusOne)
            (pi trigonometry)))

FiveNivenValues :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
FiveNivenValues reals x =
  (x == negateR reals (oneR reals)) or
  ((x ==
    negateR reals
      (divideR reals
        (oneR reals)
        (fromNatR reals twoN))) or
  ((x == zeroR reals) or
  ((x ==
    divideR reals
      (oneR reals)
      (fromNatR reals twoN)) or
  (x == oneR reals))))

niven-s-theorem : Set1
niven-s-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  (theta : R) ->
  RationalMultipleOfPi reals trigonometry theta ->
  RationalReal reals (cosine trigonometry theta) ->
  FiveNivenValues reals (cosine trigonometry theta)
