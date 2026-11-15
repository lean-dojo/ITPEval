-- Statement-only formalization of thousand-theorems corpus artifact Q1140119,
-- "Morera's theorem": on an open subset of the complex plane, a continuous
-- function into a complete normed complex vector space has vanishing
-- integrals around every contained rectangle exactly when it is complex
-- differentiable there. All analytic notions are defined below; this file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q1140119_morera_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
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

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
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

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

zeroC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

oneC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
oneC reals =
  complex (oneR reals) (zeroR reals)

addC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
addC reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

negateC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
negateC reals (complex a b) =
  complex
    (negateR reals a)
    (negateR reals b)

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

multiplyC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
multiplyC reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

record ComplexNorm
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    normC : Complex R -> R
    norm-nonnegativeC :
      (z : Complex R) ->
      lessOrEqualR reals (zeroR reals) (normC z)
    norm-zeroC :
      normC (zeroC reals) == zeroR reals
    norm-zero-onlyC :
      (z : Complex R) ->
      normC z == zeroR reals ->
      z == zeroC reals
    norm-negateC :
      (z : Complex R) ->
      normC (negateC reals z) == normC z
    norm-addC :
      (z w : Complex R) ->
      lessOrEqualR reals
        (normC (addC reals z w))
        (addR reals (normC z) (normC w))
    norm-multiplyC :
      (z w : Complex R) ->
      normC (multiplyC reals z w) ==
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
      scaleE (oneC reals) x == x
    scale-associativeE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (multiplyC reals a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : Complex R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : Complex R) ->
      (x : E) ->
      scaleE (addC reals a b) x ==
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

distanceE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)
open CompleteOrderedField
open Complex
open ComplexNorm
open NormedComplexVectorSpace

infix 4 _<N_ _<=N_

data _<N_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero <N suc n
  succ<succ : {m n : Nat} -> m <N n -> suc m <N suc n

data _<=N_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <=N n
  succ<=succ : {m n : Nat} -> m <=N n -> suc m <=N suc n

SetOf : Set -> Set1
SetOf A =
  A -> Set

Subset :
  {A : Set} ->
  SetOf A ->
  SetOf A ->
  Set
Subset {A = A} P Q =
  (x : A) ->
  P x ->
  Q x

Between :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
Between reals a b x =
  Either
    (Both
      (lessOrEqualR reals a x)
      (lessOrEqualR reals x b))
    (Both
      (lessOrEqualR reals b x)
      (lessOrEqualR reals x a))

distanceC :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  ComplexNorm reals ->
  Complex R ->
  Complex R ->
  R
distanceC {reals = reals} complexNorm z w =
  normC complexNorm (addC reals z (negateC reals w))

OpenInComplexPlane :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ComplexNorm reals ->
  SetOf (Complex R) ->
  Set
OpenInComplexPlane {R = R} reals complexNorm U =
  (z : Complex R) ->
  U z ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((w : Complex R) ->
          StrictLess reals (distanceC complexNorm w z) radius ->
          U w))

ContinuousWithinAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Complex R ->
  Set
ContinuousWithinAt {R = R}
  reals complexNorm codomain f U point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((z : Complex R) ->
          U z ->
          StrictLess reals (distanceC complexNorm z point) delta ->
          StrictLess reals
            (distanceE codomain (f z) (f point))
            epsilon))

ContinuousOn :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Set
ContinuousOn {R = R}
  reals complexNorm codomain f U =
  (point : Complex R) ->
  U point ->
  ContinuousWithinAt reals complexNorm codomain f U point

DerivativeRemainderC :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  E ->
  Complex R ->
  Complex R ->
  E
DerivativeRemainderC {reals = reals}
  codomain f derivative point z =
  subtractE codomain
    (subtractE codomain (f z) (f point))
    (scaleE codomain
      (addC reals z (negateC reals point))
      derivative)

HasComplexDerivativeWithinAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Complex R ->
  E ->
  Set
HasComplexDerivativeWithinAt {R = R}
  reals complexNorm codomain f U point derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((z : Complex R) ->
          U z ->
          StrictLess reals (distanceC complexNorm z point) delta ->
          lessOrEqualR reals
            (normE codomain
              (DerivativeRemainderC
                codomain f derivative point z))
            (multiplyR reals epsilon
              (distanceC complexNorm z point))))

DifferentiableWithinAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Complex R ->
  Set
DifferentiableWithinAt
  reals complexNorm codomain f U point =
  Exists _
    (HasComplexDerivativeWithinAt
      reals complexNorm codomain f U point)

DifferentiableOn :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Set
DifferentiableOn {R = R}
  reals complexNorm codomain f U =
  (point : Complex R) ->
  U point ->
  DifferentiableWithinAt
    reals complexNorm codomain f U point

SequentialLimit :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  (Nat -> E) ->
  E ->
  Set
SequentialLimit {R = R} {reals = reals}
  codomain sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (distanceE codomain (sequence n) limit)
        epsilon)

CauchySequence :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  (Nat -> E) ->
  Set
CauchySequence {R = R} {reals = reals}
  codomain sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals
        (distanceE codomain (sequence m) (sequence n))
        epsilon)

Complete :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {complexNorm : ComplexNorm reals} ->
  NormedComplexVectorSpace reals complexNorm E ->
  Set
Complete {E = E} codomain =
  (sequence : Nat -> E) ->
  CauchySequence codomain sequence ->
  Exists E (\ limit -> SequentialLimit codomain sequence limit)

TaggedPartition :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Nat ->
  (Nat -> R) ->
  (Nat -> R) ->
  Set
TaggedPartition reals lower upper count nodes tags =
  Both
    (nodes zero == lower)
    (Both
      (nodes count == upper)
      (Both
        ((k : Nat) ->
          k <N count ->
          StrictLess reals (nodes k) (nodes (suc k)))
        ((k : Nat) ->
          k <N count ->
          Both
            (lessOrEqualR reals (nodes k) (tags k))
            (lessOrEqualR reals (tags k) (nodes (suc k))))))

PartitionMeshBelow :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  {lower upper : R} ->
  {count : Nat} ->
  {nodes tags : Nat -> R} ->
  TaggedPartition reals lower upper count nodes tags ->
  R ->
  Set
PartitionMeshBelow reals {count = count} {nodes = nodes}
  partition delta =
  (k : Nat) ->
  k <N count ->
  StrictLess reals
    (addR reals
      (nodes (suc k))
      (negateR reals (nodes k)))
    delta

riemannSumE :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (R -> E) ->
  (Nat -> R) ->
  (Nat -> R) ->
  Nat ->
  E
riemannSumE reals codomain integrand nodes tags zero =
  zeroE codomain
riemannSumE reals codomain integrand nodes tags (suc n) =
  addE codomain
    (riemannSumE reals codomain integrand nodes tags n)
    (scaleE codomain
      (complex
        (addR reals
          (nodes (suc n))
          (negateR reals (nodes n)))
        (zeroR reals))
      (integrand (tags n)))

RiemannIntegralIncreasing :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  {complexNorm : ComplexNorm reals} ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  R ->
  R ->
  (R -> E) ->
  E ->
  Set
RiemannIntegralIncreasing {R = R}
  reals codomain lower upper integrand value =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((count : Nat) ->
          (nodes tags : Nat -> R) ->
          (partition :
            TaggedPartition
              reals lower upper count nodes tags) ->
          PartitionMeshBelow reals partition delta ->
          StrictLess reals
            (distanceE codomain
              (riemannSumE
                reals codomain integrand nodes tags count)
              value)
            epsilon))

data OrientedRiemannIntegralValue
  {R E : Set}
  (reals : CompleteOrderedField R)
  {complexNorm : ComplexNorm reals}
  (codomain : NormedComplexVectorSpace reals complexNorm E)
  (lower upper : R)
  (integrand : R -> E)
  (value : E) : Set where
  forwardIntegral :
    lessOrEqualR reals lower upper ->
    RiemannIntegralIncreasing
      reals codomain lower upper integrand value ->
    OrientedRiemannIntegralValue
      reals codomain lower upper integrand value
  backwardIntegral :
    lessOrEqualR reals upper lower ->
    RiemannIntegralIncreasing
      reals codomain upper lower integrand
      (negateE codomain value) ->
    OrientedRiemannIntegralValue
      reals codomain lower upper integrand value

RectangleSubset :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  Complex R ->
  Complex R ->
  SetOf (Complex R) ->
  Set
RectangleSubset reals z w U =
  (x y : _) ->
  Between reals (realPart z) (realPart w) x ->
  Between reals (imaginaryPart z) (imaginaryPart w) y ->
  U (complex x y)

record WedgeIntegralValue
  {R E : Set}
  (reals : CompleteOrderedField R)
  {complexNorm : ComplexNorm reals}
  (codomain : NormedComplexVectorSpace reals complexNorm E)
  (z w : Complex R)
  (f : Complex R -> E)
  (value : E) : Set where
  field
    horizontalValue verticalValue : E
    horizontalIntegral :
      OrientedRiemannIntegralValue
        reals codomain
        (realPart z) (realPart w)
        (\ x -> f (complex x (imaginaryPart z)))
        horizontalValue
    verticalIntegral :
      OrientedRiemannIntegralValue
        reals codomain
        (imaginaryPart z) (imaginaryPart w)
        (\ y -> f (complex (realPart w) y))
        verticalValue
    combines :
      value ==
      addE codomain horizontalValue
        (scaleE codomain
          (complex (zeroR reals) (oneR reals))
          verticalValue)

IsConservativeOn :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  (Complex R -> E) ->
  SetOf (Complex R) ->
  Set
IsConservativeOn {E = E}
  reals complexNorm codomain f U =
  (z w : _) ->
  RectangleSubset reals z w U ->
  Exists E
    (\ forwardValue ->
      Both
        (WedgeIntegralValue
          reals codomain z w f forwardValue)
        (Exists E
          (\ reverseValue ->
            Both
              (WedgeIntegralValue
                reals codomain w z f reverseValue)
              (forwardValue ==
                negateE codomain reverseValue))))

morera-theorem : Set2
morera-theorem =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (codomain : NormedComplexVectorSpace reals complexNorm E) ->
  Complete codomain ->
  (U : SetOf (Complex R)) ->
  OpenInComplexPlane reals complexNorm U ->
  (f : Complex R -> E) ->
  Iff
    (Both
      (IsConservativeOn reals complexNorm codomain f U)
      (ContinuousOn reals complexNorm codomain f U))
    (DifferentiableOn reals complexNorm codomain f U)
