-- Statement-only formalization of thousand-theorems corpus artifact Q3527250,
-- "Hadamard three-lines theorem": the norm of a bounded, closed-strip
-- continuous and interior-holomorphic function is bounded by the canonical
-- interpolation of its two vertical-line norm suprema. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3527250_hadamard_three_lines_theorem where

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

data _<=N_ : Nat -> Nat -> Set where
  zero<= :
    {n : Nat} ->
    zero <=N n
  suc<=suc :
    {m n : Nat} ->
    m <=N n ->
    suc m <=N suc n

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
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

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

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) ->
      forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) ->
      backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

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
  multiplyR reals x (reciprocalR reals y)

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

powerNatR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerNatR reals x zero =
  oneR reals
powerNatR reals x (suc n) =
  multiplyR reals (powerNatR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

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

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x n =
  sumFirstR reals
    (\ k ->
      divideR reals
        (powerNatR reals x k)
        (fromNatR reals (factorial k)))
    n

RealSequenceLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
RealSequenceLimit {R = R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteR reals
          (subtractR reals (sequence n) limit))
        epsilon)

ExponentialValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
ExponentialValue reals exponent value =
  RealSequenceLimit reals
    (exponentialPartialSum reals exponent)
    value

PositiveLogarithmValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
PositiveLogarithmValue reals base logarithm =
  Both
    (Positive reals base)
    (ExponentialValue reals logarithm base)

CanonicalPositiveRealPowerValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CanonicalPositiveRealPowerValue {R = R} reals base exponent value =
  Exists R
    (\ logarithm ->
      Both
        (PositiveLogarithmValue reals base logarithm)
        (ExponentialValue reals
          (multiplyR reals exponent logarithm)
          value))

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

complexFromReal :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Complex R
complexFromReal reals x =
  complex x (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

complexNegate :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
complexNegate reals (complex a b) =
  complex
    (negateR reals a)
    (negateR reals b)

complexSubtract :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexSubtract reals z w =
  complexAdd reals z (complexNegate reals w)

complexMultiply :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

complexDivideByReal :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  R ->
  Complex R
complexDivideByReal reals (complex a b) denominator =
  complex
    (divideR reals a denominator)
    (divideR reals b denominator)

record ComplexNorm
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    normC : Complex R -> R
    norm-nonnegativeC :
      (z : Complex R) ->
      lessOrEqualR reals (zeroR reals) (normC z)
    norm-zeroC :
      normC (complexZero reals) == zeroR reals
    norm-zero-onlyC :
      (z : Complex R) ->
      normC z == zeroR reals ->
      z == complexZero reals
    norm-negateC :
      (z : Complex R) ->
      normC (complexNegate reals z) == normC z
    norm-addC :
      (z w : Complex R) ->
      lessOrEqualR reals
        (normC (complexAdd reals z w))
        (addR reals (normC z) (normC w))
    norm-multiplyC :
      (z w : Complex R) ->
      normC (complexMultiply reals z w) ==
      multiplyR reals (normC z) (normC w)
    norm-squareC :
      (z : Complex R) ->
      multiplyR reals (normC z) (normC z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))

open ComplexNorm

record NormedComplexVectorSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (complexNorm : ComplexNorm reals)
  (E : Set) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : Complex R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) ->
      scaleE (complexOne reals) x == x
    scale-associativeE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (complexMultiply reals a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : Complex R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (complexAdd reals a b) x ==
      addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE == zeroR reals
    norm-zero-onlyE :
      (x : E) ->
      normE x == zeroR reals ->
      x == zeroE
    norm-negateE :
      (x : E) ->
      normE (negateE x) == normE x
    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scaleE :
      (a : Complex R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (normC complexNorm a) (normE x)

open NormedComplexVectorSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

InOpenVerticalStrip :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Complex R ->
  Set
InOpenVerticalStrip reals lower upper z =
  Both
    (StrictLess reals lower (realPart z))
    (StrictLess reals (realPart z) upper)

InClosedVerticalStrip :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Complex R ->
  Set
InClosedVerticalStrip reals lower upper z =
  Both
    (lessOrEqualR reals lower (realPart z))
    (lessOrEqualR reals (realPart z) upper)

ContinuousWithinClosedStripAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  R ->
  R ->
  Complex R ->
  Set
ContinuousWithinClosedStripAt {R = R} reals complexNorm space
  function lower upper point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((z : Complex R) ->
          InClosedVerticalStrip reals lower upper z ->
          StrictLess reals
            (normC complexNorm (complexSubtract reals z point))
            delta ->
          StrictLess reals
            (normE space
              (subtractE space (function z) (function point)))
            epsilon))

ContinuousOnClosedStrip :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  R ->
  R ->
  Set
ContinuousOnClosedStrip {R = R} reals complexNorm space
  function lower upper =
  (point : Complex R) ->
  InClosedVerticalStrip reals lower upper point ->
  ContinuousWithinClosedStripAt
    reals complexNorm space function lower upper point

ComplexDifferentiableAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  Complex R ->
  Set
ComplexDifferentiableAt {R = R} {E = E}
  reals complexNorm space function point =
  Exists E
    (\ derivative ->
      (epsilon : R) ->
      Positive reals epsilon ->
      Exists R
        (\ delta ->
          Both
            (Positive reals delta)
            ((z : Complex R) ->
              StrictLess reals
                (normC complexNorm
                  (complexSubtract reals z point))
                delta ->
              lessOrEqualR reals
                (normE space
                  (subtractE space
                    (subtractE space
                      (function z)
                      (function point))
                    (scaleE space
                      (complexSubtract reals z point)
                      derivative)))
                (multiplyR reals epsilon
                  (normC complexNorm
                    (complexSubtract reals z point))))))

DifferentiableOnOpenStrip :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  R ->
  R ->
  Set
DifferentiableOnOpenStrip {R = R} reals complexNorm space
  function lower upper =
  (point : Complex R) ->
  InOpenVerticalStrip reals lower upper point ->
  ComplexDifferentiableAt reals complexNorm space function point

BoundedOnClosedStrip :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  (Complex R -> E) ->
  R ->
  R ->
  Set
BoundedOnClosedStrip {R = R} reals space function lower upper =
  Exists R
    (\ bound ->
      (z : Complex R) ->
      InClosedVerticalStrip reals lower upper z ->
      lessOrEqualR reals (normE space (function z)) bound)

SupNormOnVerticalLine :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  (Complex R -> E) ->
  R ->
  R ->
  Set
SupNormOnVerticalLine {R = R} reals space function line supremum =
  Both
    ((z : Complex R) ->
      realPart z == line ->
      lessOrEqualR reals (normE space (function z)) supremum)
    ((upperBound : R) ->
      ((z : Complex R) ->
        realPart z == line ->
        lessOrEqualR reals
          (normE space (function z))
          upperBound) ->
      lessOrEqualR reals supremum upperBound)

normalizedComplexParameter :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Complex R ->
  Complex R
normalizedComplexParameter reals lower upper z =
  complexDivideByReal reals
    (complexSubtract reals z (complexFromReal reals lower))
    (subtractR reals upper lower)

leftInterpolationExponent :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Complex R ->
  Complex R
leftInterpolationExponent reals lower upper z =
  complexSubtract reals
    (complexOne reals)
    (normalizedComplexParameter reals lower upper z)

CanonicalComplexPowerNormValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Complex R ->
  R ->
  Set
CanonicalComplexPowerNormValue reals base exponent value =
  CanonicalPositiveRealPowerValue reals
    base
    (realPart exponent)
    value

ZeroBoundarySupremum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
ZeroBoundarySupremum reals leftSupremum rightSupremum =
  Either
    (leftSupremum == zeroR reals)
    (rightSupremum == zeroR reals)

InterpStripPrimeNormBound :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (function : Complex R -> E) ->
  (z : Complex R) ->
  (lower upper leftSupremum rightSupremum : R) ->
  Set
InterpStripPrimeNormBound {R = R} {E = E}
  reals space function z lower upper
  leftSupremum rightSupremum =
  Either
    (Both
      (ZeroBoundarySupremum reals leftSupremum rightSupremum)
      (lessOrEqualR reals
        (normE space (function z))
        (zeroR reals)))
    (Both
      (Not (ZeroBoundarySupremum reals leftSupremum rightSupremum))
      (Exists R
        (\ leftPowerNorm ->
          Both
            (CanonicalComplexPowerNormValue reals
              leftSupremum
              (leftInterpolationExponent reals lower upper z)
              leftPowerNorm)
            (Exists R
              (\ rightPowerNorm ->
                Both
                  (CanonicalComplexPowerNormValue reals
                    rightSupremum
                    (normalizedComplexParameter reals lower upper z)
                    rightPowerNorm)
                  (lessOrEqualR reals
                    (normE space (function z))
                    (multiplyR reals
                      leftPowerNorm
                      rightPowerNorm)))))))

SupremumInterpolationConclusion :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (function : Complex R -> E) ->
  (z : Complex R) ->
  R ->
  R ->
  Set
SupremumInterpolationConclusion {R = R} reals space function z lower upper =
  Exists R
    (\ leftSupremum ->
      Both
        (SupNormOnVerticalLine reals space
          function lower leftSupremum)
        (Exists R
          (\ rightSupremum ->
            Both
              (SupNormOnVerticalLine reals space
                function upper rightSupremum)
              (InterpStripPrimeNormBound reals space function z
                lower upper leftSupremum rightSupremum))))

hadamard-three-lines-theorem : Set2
hadamard-three-lines-theorem =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (space : NormedComplexVectorSpace reals complexNorm E) ->
  (function : Complex R -> E) ->
  (z : Complex R) ->
  (lower upper : R) ->
  StrictLess reals lower upper ->
  InClosedVerticalStrip reals lower upper z ->
  ContinuousOnClosedStrip
    reals complexNorm space function lower upper ->
  DifferentiableOnOpenStrip
    reals complexNorm space function lower upper ->
  BoundedOnClosedStrip reals space function lower upper ->
  SupremumInterpolationConclusion reals space
    function z lower upper
