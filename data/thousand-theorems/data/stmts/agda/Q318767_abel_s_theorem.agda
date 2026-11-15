-- Statement-only formalization of thousand-theorems corpus artifact Q318767,
-- "Abel's theorem": a convergent real or complex coefficient series gives a
-- power series tending to the same sum from the real left or within any
-- positive-width complex Stolz cone at one. This file contains no proof.

{-# OPTIONS --safe #-}

module Q318767_abel_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
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
      Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

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
    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-addR :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
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
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

squareR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
squareR reals x =
  multiplyR reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

RealClose :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
RealClose reals center radius x =
  StrictLess reals
    (absoluteR reals (subtractR reals x center))
    radius

sumFirstR :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirstR reals terms zero =
  zeroR reals
sumFirstR reals terms (suc n) =
  addR reals
    (sumFirstR reals terms n)
    (terms n)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

RealSequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
RealSequentialLimit reals sequence limit =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      RealClose reals limit epsilon (sequence n))

RealPowerSeriesSumAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  R ->
  Set
RealPowerSeriesSumAt reals coefficients x limit =
  RealSequentialLimit reals
    (\ n ->
      sumFirstR reals
        (\ i ->
          multiplyR reals
            (coefficients i)
            (powerR reals x i))
        n)
    limit

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals x y =
  complex
    (addR reals (realPart x) (realPart y))
    (addR reals (imaginaryPart x) (imaginaryPart y))

complexNegate :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
complexNegate reals x =
  complex
    (negateR reals (realPart x))
    (negateR reals (imaginaryPart x))

complexSubtract :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexSubtract reals x y =
  complexAdd reals x (complexNegate reals y)

complexMultiply :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals x y =
  complex
    (subtractR reals
      (multiplyR reals (realPart x) (realPart y))
      (multiplyR reals (imaginaryPart x) (imaginaryPart y)))
    (addR reals
      (multiplyR reals (realPart x) (imaginaryPart y))
      (multiplyR reals (imaginaryPart x) (realPart y)))

complexPower :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Nat ->
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals (complexPower reals z n) z

complexNormSquared :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  R
complexNormSquared reals z =
  addR reals
    (squareR reals (realPart z))
    (squareR reals (imaginaryPart z))

ComplexClose :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  R ->
  Complex R ->
  Set
ComplexClose reals center radius z =
  StrictLess reals
    (complexNormSquared reals (complexSubtract reals z center))
    (squareR reals radius)

sumFirstC :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> Complex R) ->
  Nat ->
  Complex R
sumFirstC reals terms zero =
  complexZero reals
sumFirstC reals terms (suc n) =
  complexAdd reals
    (sumFirstC reals terms n)
    (terms n)

ComplexSequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> Complex R) ->
  Complex R ->
  Set
ComplexSequentialLimit reals sequence limit =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      ComplexClose reals limit epsilon (sequence n))

ComplexPowerSeriesSumAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> Complex R) ->
  Complex R ->
  Complex R ->
  Set
ComplexPowerSeriesSumAt reals coefficients z limit =
  ComplexSequentialLimit reals
    (\ n ->
      sumFirstC reals
        (\ i ->
          complexMultiply reals
            (coefficients i)
            (complexPower reals z i))
        n)
    limit

StolzCone :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Complex R ->
  Set
StolzCone reals s z =
  StrictLess reals
    (absoluteR reals (imaginaryPart z))
    (multiplyR reals s
      (subtractR reals (oneR reals) (realPart z)))

ComplexPowerSeriesTendsWithinStolzCone :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> Complex R) ->
  Complex R ->
  R ->
  Set
ComplexPowerSeriesTendsWithinStolzCone {R = R}
  reals coefficients limit s =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((z : Complex R) ->
          StolzCone reals s z ->
          ComplexClose reals (complexOne reals) delta z ->
          Exists (Complex R)
            (\ value ->
              Both
                (ComplexPowerSeriesSumAt reals coefficients z value)
                (ComplexClose reals limit epsilon value))))

RealPowerSeriesTendsFromLeft :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
RealPowerSeriesTendsFromLeft {R = R} reals coefficients limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((x : R) ->
          StrictLess reals x (oneR reals) ->
          RealClose reals (oneR reals) delta x ->
          Exists R
            (\ value ->
              Both
                (RealPowerSeriesSumAt reals coefficients x value)
                (RealClose reals limit epsilon value))))

complex-tendsto-tsum-power-series-within-stolz-cone : Set1
complex-tendsto-tsum-power-series-within-stolz-cone =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (coefficients : Nat -> Complex R) ->
  (limit : Complex R) ->
  ComplexSequentialLimit reals
    (\ n -> sumFirstC reals coefficients n)
    limit ->
  (s : R) ->
  Positive reals s ->
  ComplexPowerSeriesTendsWithinStolzCone
    reals coefficients limit s

real-tendsto-tsum-power-series-within-left : Set1
real-tendsto-tsum-power-series-within-left =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (coefficients : Nat -> R) ->
  (limit : R) ->
  RealSequentialLimit reals
    (\ n -> sumFirstR reals coefficients n)
    limit ->
  RealPowerSeriesTendsFromLeft reals coefficients limit
