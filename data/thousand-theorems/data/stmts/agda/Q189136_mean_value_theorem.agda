-- Statement-only formalization of thousand-theorems corpus artifact Q189136,
-- "Mean value theorem": the Lagrange derivative-equals-secant-slope form and
-- Cauchy's cross-multiplied ratio form for real functions on an interval.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q189136_mean_value_theorem where

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

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius point =
  Both
    (StrictLess reals (subtractR reals center radius) point)
    (StrictLess reals point (addR reals center radius))

ClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
ClosedInterval reals lower upper point =
  Both
    (lessOrEqualR reals lower point)
    (lessOrEqualR reals point upper)

OpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
OpenInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (StrictLess reals point upper)

ContinuousWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
ContinuousWithinAt {R} reals function domain point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          domain y ->
          CloseTo reals point delta y ->
          CloseTo reals (function point) epsilon (function y)))

ContinuousOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  Set
ContinuousOn {R} reals function domain =
  (point : R) ->
  domain point ->
  ContinuousWithinAt reals function domain point

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point y =
  divideR reals
    (subtractR reals (function y) (function point))
    (subtractR reals y point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          CloseTo reals point delta y ->
          y != point ->
          CloseTo reals derivative epsilon
            (differenceQuotient reals function point y)))

DifferentiableOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  Set
DifferentiableOn {R} reals function domain =
  (point : R) ->
  domain point ->
  Exists R
    (\ derivative ->
      DerivativeAt reals function point derivative)

exists-deriv-eq-slope : Set2
exists-deriv-eq-slope =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f : R -> R) ->
  (a b : R) ->
  StrictLess reals a b ->
  ContinuousOn reals f (ClosedInterval reals a b) ->
  DifferentiableOn reals f (OpenInterval reals a b) ->
  Exists R
    (\ c ->
      Both
        (OpenInterval reals a b c)
        (Exists R
          (\ derivative-f ->
            Both
              (DerivativeAt reals f c derivative-f)
              (derivative-f ==
                divideR reals
                  (subtractR reals (f b) (f a))
                  (subtractR reals b a)))))

exists-ratio-deriv-eq-ratio-slope : Set2
exists-ratio-deriv-eq-ratio-slope =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (f g : R -> R) ->
  (a b : R) ->
  StrictLess reals a b ->
  ContinuousOn reals f (ClosedInterval reals a b) ->
  DifferentiableOn reals f (OpenInterval reals a b) ->
  ContinuousOn reals g (ClosedInterval reals a b) ->
  DifferentiableOn reals g (OpenInterval reals a b) ->
  Exists R
    (\ c ->
      Both
        (OpenInterval reals a b c)
        (Exists R
          (\ derivative-f ->
            Exists R
              (\ derivative-g ->
                Both
                  (DerivativeAt reals f c derivative-f)
                  (Both
                    (DerivativeAt reals g c derivative-g)
                    (multiplyR reals
                      (subtractR reals (g b) (g a))
                      derivative-f
                    ==
                    multiplyR reals
                      (subtractR reals (f b) (f a))
                      derivative-g))))))
