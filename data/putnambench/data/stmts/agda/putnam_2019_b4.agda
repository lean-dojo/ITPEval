-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_b4
-- (putnambench__agda__putnam_2019_b4): every twice continuously
-- differentiable solution of the two stated partial differential equations
-- on x >= 1 and y >= 1 has mixed finite-difference minimum
-- 2 * ln 2 - 1 / 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2019B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

fromNat :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
fromNat reals zero =
  zeroR reals
fromNat reals (suc n) =
  add reals (fromNat reals n) (oneR reals)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

data NatLessOrEqual : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    NatLessOrEqual zero n
  successor-less-or-equal :
    {m n : Nat} ->
    NatLessOrEqual m n ->
    NatLessOrEqual (suc m) (suc n)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

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
      NatLessOrEqual cutoff n ->
      CloseTo reals limit epsilon (sequence n))

midpointRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Nat ->
  R
midpointRiemannSum reals lower upper function pieces =
  let
    step =
      divide reals
        (subtract reals upper lower)
        (fromNat reals pieces)
    half-step =
      divide reals step (fromNat reals twoN)
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (add reals lower
            (add reals
              (multiply reals
                (fromNat reals i)
                step)
              half-step)))
        step)

NaturalLogValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
NaturalLogValue reals x value =
  ConvergesTo reals
    (\ n ->
      midpointRiemannSum reals
        (oneR reals)
        x
        (inverse reals)
        (suc n))
    value

record RealAnalysis (R : Set) : Set1 where
  field
    reals : CompleteOrderedRealField R
    naturalLog : R -> R
    natural-log-definition :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      NaturalLogValue reals x (naturalLog x)

open RealAnalysis

AtLeastOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
AtLeastOne reals x =
  lessOrEqual reals (oneR reals) x

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals domain function point derivative-value =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        domain x ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative-value epsilon
          (divide reals
            (subtract reals (function x) (function point))
            (subtract reals x point))))

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

InQuadrant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Set
InQuadrant reals p =
  AtLeastOne reals (x-coordinate p)
  and
  AtLeastOne reals (y-coordinate p)

ClosePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
ClosePoint reals center radius p =
  CloseTo reals
    (x-coordinate center)
    radius
    (x-coordinate p)
  and
  CloseTo reals
    (y-coordinate center)
    radius
    (y-coordinate p)

ContinuousWithinQuadrantAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  Point R ->
  Set
ContinuousWithinQuadrantAt {R} reals function center =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((p : Point R) ->
        InQuadrant reals p ->
        ClosePoint reals center delta p ->
        CloseTo reals
          (function center)
          epsilon
          (function p)))

x-slice :
  {R : Set} ->
  (Point R -> R) ->
  Point R ->
  R ->
  R
x-slice function p x =
  function (point x (y-coordinate p))

y-slice :
  {R : Set} ->
  (Point R -> R) ->
  Point R ->
  R ->
  R
y-slice function p y =
  function (point (x-coordinate p) y)

record SecondPartialData
  {R : Set}
  (analysis : RealAnalysis R)
  (function : Point R -> R) :
  Set where

  field
    fx fy fxx fxy fyx fyy : Point R -> R

    derivative-x :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (x-slice function p)
        (x-coordinate p)
        (fx p)

    derivative-y :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (y-slice function p)
        (y-coordinate p)
        (fy p)

    derivative-xx :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (x-slice fx p)
        (x-coordinate p)
        (fxx p)

    derivative-xy :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (y-slice fx p)
        (y-coordinate p)
        (fxy p)

    derivative-yx :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (x-slice fy p)
        (x-coordinate p)
        (fyx p)

    derivative-yy :
      (p : Point R) ->
      InQuadrant (reals analysis) p ->
      DerivativeWithinAt
        (reals analysis)
        (AtLeastOne (reals analysis))
        (y-slice fy p)
        (y-coordinate p)
        (fyy p)

open SecondPartialData

ContinuousOnQuadrant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  Set
ContinuousOnQuadrant {R} reals function =
  (p : Point R) ->
  InQuadrant reals p ->
  ContinuousWithinQuadrantAt reals function p

C2OnQuadrant :
  {R : Set} ->
  {analysis : RealAnalysis R} ->
  {function : Point R -> R} ->
  SecondPartialData analysis function ->
  Set
C2OnQuadrant {R} {analysis} {function} derivatives =
  let real-field = reals analysis in
  ContinuousOnQuadrant real-field function
  and
  ContinuousOnQuadrant real-field (fx derivatives)
  and
  ContinuousOnQuadrant real-field (fy derivatives)
  and
  ContinuousOnQuadrant real-field (fxx derivatives)
  and
  ContinuousOnQuadrant real-field (fxy derivatives)
  and
  ContinuousOnQuadrant real-field (fyx derivatives)
  and
  ContinuousOnQuadrant real-field (fyy derivatives)

SatisfiesEquations :
  {R : Set} ->
  {analysis : RealAnalysis R} ->
  {function : Point R -> R} ->
  SecondPartialData analysis function ->
  Set
SatisfiesEquations {R} {analysis} derivatives =
  let
    real-field = reals analysis
    log = naturalLog analysis
  in
  ((p : Point R) ->
    InQuadrant real-field p ->
    let
      x = x-coordinate p
      y = y-coordinate p
    in
    add real-field
      (multiply real-field x (fx derivatives p))
      (multiply real-field y (fy derivatives p))
    ==
    multiply real-field
      (multiply real-field x y)
      (log (multiply real-field x y)))
  and
  ((p : Point R) ->
    InQuadrant real-field p ->
    let
      x = x-coordinate p
      y = y-coordinate p
    in
    add real-field
      (multiply real-field
        (square real-field x)
        (fxx derivatives p))
      (multiply real-field
        (square real-field y)
        (fyy derivatives p))
    ==
    multiply real-field x y)

AdmissibleFunction :
  {R : Set} ->
  (analysis : RealAnalysis R) ->
  (Point R -> R) ->
  Set
AdmissibleFunction analysis function =
  Exists (SecondPartialData analysis function)
    (\ derivatives ->
      C2OnQuadrant derivatives
      and
      SatisfiesEquations derivatives)

mixedDifference :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  R ->
  R
mixedDifference reals function s =
  let
    s-plus-one = add reals s (oneR reals)
  in
  add reals
    (subtract reals
      (subtract reals
        (function (point s-plus-one s-plus-one))
        (function (point s-plus-one s)))
      (function (point s s-plus-one)))
    (function (point s s))

IsMinimumValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
IsMinimumValue {R} reals function domain minimum =
  Exists R
    (\ s ->
      domain s
      and
      function s == minimum)
  and
  ((s : R) ->
    domain s ->
    lessOrEqual reals minimum (function s))

putnamSolution :
  {R : Set} ->
  RealAnalysis R ->
  R
putnamSolution analysis =
  let
    real-field = reals analysis
    two = fromNat real-field twoN
  in
  subtract real-field
    (multiply real-field
      two
      (naturalLog analysis two))
    (divide real-field
      (oneR real-field)
      two)

putnam-2019-b4 : Set1
putnam-2019-b4 =
  (R : Set) ->
  (analysis : RealAnalysis R) ->
  (function : Point R -> R) ->
  AdmissibleFunction analysis function ->
  IsMinimumValue
    (reals analysis)
    (mixedDifference (reals analysis) function)
    (AtLeastOne (reals analysis))
    (putnamSolution analysis)
