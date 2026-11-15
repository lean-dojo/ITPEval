-- Statement-only formalization of thousand-theorems corpus artifact Q727102,
-- "Fermat's theorem (stationary points)": the totalized scalar derivative
-- and Frechet derivative of a real-valued function at a local extremum are zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q727102_fermat_s_theorem_stationary_points where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Both10 (A : Set1) (B : Set) : Set1 where
  constructor both10
  field
    first10  : A
    second10 : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

data Either01 (A : Set) (B : Set1) : Set1 where
  left01  : A -> Either01 A B
  right01 : B -> Either01 A B

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
    absolute-zeroR :
      absoluteR zeroR == zeroR
    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negateR :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-addR :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)
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
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
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

CloseToR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseToR reals center radius point =
  StrictLess reals
    (absoluteR reals (subtractR reals point center))
    radius

record NormedVectorSpace
  (R E : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) -> scaleE (oneR reals) x == x
    scale-associativeE :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x == scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) == addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x == addE (scaleE a x) (scaleE b x)

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
      (a : R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (absoluteR reals a) (normE x)

open NormedVectorSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

CloseToE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  R ->
  E ->
  Set
CloseToE {reals = reals} space center radius point =
  StrictLess reals (distanceE space point center) radius

record ContinuousLinearFunctional
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals) : Set1 where
  field
    apply :
      E -> R
    map-add :
      (x y : E) ->
      apply (addE space x y) ==
      addR reals (apply x) (apply y)
    map-scale :
      (a : R) ->
      (x : E) ->
      apply (scaleE space a x) ==
      multiplyR reals a (apply x)
    operator-bound :
      R
    operator-bound-nonnegative :
      lessOrEqualR reals (zeroR reals) operator-bound
    bounded :
      (x : E) ->
      lessOrEqualR reals
        (absoluteR reals (apply x))
        (multiplyR reals operator-bound (normE space x))

open ContinuousLinearFunctional

DerivativeRemainder :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (f : E -> R) ->
  ContinuousLinearFunctional reals space ->
  E ->
  E ->
  R
DerivativeRemainder {reals = reals} space f derivative point y =
  subtractR reals
    (subtractR reals (f y) (f point))
    (apply derivative (subtractE space y point))

HasFDerivAt :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (f : E -> R) ->
  ContinuousLinearFunctional reals space ->
  E ->
  Set
HasFDerivAt {R = R} {reals = reals} space f derivative point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          CloseToE space point radius y ->
          lessOrEqualR reals
            (absoluteR reals
              (DerivativeRemainder space f derivative point y))
            (multiplyR reals epsilon
              (distanceE space y point))))

IsLocalMinE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (E -> R) ->
  E ->
  Set
IsLocalMinE {R = R} {E = E} {reals = reals} space f point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : E) ->
          CloseToE space point radius y ->
          lessOrEqualR reals (f point) (f y)))

IsLocalMaxE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (E -> R) ->
  E ->
  Set
IsLocalMaxE {R = R} {E = E} {reals = reals} space f point =
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : E) ->
          CloseToE space point radius y ->
          lessOrEqualR reals (f y) (f point)))

IsLocalExtrE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (E -> R) ->
  E ->
  Set
IsLocalExtrE space f point =
  Either
    (IsLocalMinE space f point)
    (IsLocalMaxE space f point)

FDerivativeEqualsZero :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  ContinuousLinearFunctional reals space ->
  Set
FDerivativeEqualsZero {E = E} {reals = reals} space derivative =
  (x : E) ->
  apply derivative x == zeroR reals

IsTotalizedFDerivativeAt :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (E -> R) ->
  E ->
  ContinuousLinearFunctional reals space ->
  Set1
IsTotalizedFDerivativeAt {reals = reals} space f point derivative =
  Either01
    (HasFDerivAt space f derivative point)
    (Both10
      ((candidate : ContinuousLinearFunctional reals space) ->
        Not (HasFDerivAt space f candidate point))
      (FDerivativeEqualsZero space derivative))

TotalizedFDerivativeEqualsZero :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  (space : NormedVectorSpace R E reals) ->
  (E -> R) ->
  E ->
  Set1
TotalizedFDerivativeEqualsZero {E = E} {reals = reals}
  space f point =
  (derivative : ContinuousLinearFunctional reals space) ->
  IsTotalizedFDerivativeAt space f point derivative ->
  FDerivativeEqualsZero space derivative

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals f point y =
  divideR reals
    (subtractR reals (f y) (f point))
    (subtractR reals y point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals f point derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : R) ->
          CloseToR reals point radius y ->
          y != point ->
          CloseToR reals derivative epsilon
            (differenceQuotient reals f point y)))

IsLocalMinR :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
IsLocalMinR reals f point =
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          CloseToR reals point radius y ->
          lessOrEqualR reals (f point) (f y)))

IsLocalMaxR :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
IsLocalMaxR reals f point =
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          CloseToR reals point radius y ->
          lessOrEqualR reals (f y) (f point)))

IsLocalExtrR :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
IsLocalExtrR reals f point =
  Either
    (IsLocalMinR reals f point)
    (IsLocalMaxR reals f point)

IsTotalizedDerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
IsTotalizedDerivativeAt {R} reals f point derivative =
  Either
    (DerivativeAt reals f point derivative)
    (Both
      (Not
        (Exists R
          (\ candidate ->
            DerivativeAt reals f point candidate)))
      (derivative == zeroR reals))

TotalizedDerivativeEqualsZero :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
TotalizedDerivativeEqualsZero reals f point =
  (derivative : _) ->
  IsTotalizedDerivativeAt reals f point derivative ->
  derivative == zeroR reals

fermat-fderiv-eq-zero : Set2
fermat-fderiv-eq-zero =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  (f : E -> R) ->
  (point : E) ->
  IsLocalExtrE space f point ->
  TotalizedFDerivativeEqualsZero space f point

fermat-deriv-eq-zero : Set2
fermat-deriv-eq-zero =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (point : R) ->
  IsLocalExtrR reals f point ->
  TotalizedDerivativeEqualsZero reals f point
