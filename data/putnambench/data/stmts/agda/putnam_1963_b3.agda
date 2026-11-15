-- Statement-only formalization of PutnamBench corpus artifact putnam_1963_b3:
-- every twice-differentiable real solution of the given quadratic functional
-- equation is exactly a scaled hyperbolic sine, linear, or scaled sine family.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

two :
  {R : Set} ->
  CompleteOrderedField R ->
  R
two reals =
  add reals (oneR reals) (oneR reals)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

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
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals (negate reals (oneR reals)) n

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

sineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (suc ((suc (suc zero)) * n))))
    (fromNat reals
      (factorial (suc ((suc (suc zero)) * n))))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals (exponentialTerm reals x) value

SineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
SineValue reals x value =
  SeriesHasSum reals (sineTerm reals x) value

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

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
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

Differentiable :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
Differentiable {R} reals function =
  (x : R) ->
  Exists R (DerivativeAt reals function x)

TwiceDifferentiable :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
TwiceDifferentiable {R} reals function =
  Exists (R -> R)
    (\ firstDerivative ->
      ((x : R) ->
        DerivativeAt reals function x (firstDerivative x))
      and
      Differentiable reals firstDerivative)

SameFunction :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
SameFunction {A} leftFunction rightFunction =
  (x : A) ->
  leftFunction x == rightFunction x

HyperbolicSineFamily :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  (R -> R) ->
  Set
HyperbolicSineFamily {R} reals A k function =
  (x : R) ->
  Exists R
    (\ positiveExponential ->
      Exists R
        (\ negativeExponential ->
          ExponentialValue reals
            (multiply reals k x)
            positiveExponential
          and
          ExponentialValue reals
            (negate reals (multiply reals k x))
            negativeExponential
          and
          function x ==
            multiply reals A
              (divide reals
                (subtract reals
                  positiveExponential
                  negativeExponential)
                (two reals))))

LinearFamily :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  (R -> R) ->
  Set
LinearFamily reals A function =
  SameFunction function
    (\ x -> multiply reals A x)

SineFamily :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  (R -> R) ->
  Set
SineFamily {R} reals A k function =
  (x : R) ->
  Exists R
    (\ sineValue ->
      SineValue reals
        (multiply reals k x)
        sineValue
      and
      function x == multiply reals A sineValue)

Solution :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
Solution {R} reals function =
  Exists R
    (\ A ->
      Exists R
        (\ k ->
          HyperbolicSineFamily reals A k function
          or
          (LinearFamily reals A function
          or
          SineFamily reals A k function)))

FunctionalEquation :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
FunctionalEquation {R} reals function =
  (x y : R) ->
  subtract reals
    (square reals (function x))
    (square reals (function y))
  ==
  multiply reals
    (function (add reals x y))
    (function (subtract reals x y))

putnam-1963-b3 : Set1
putnam-1963-b3 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (function : R -> R) ->
  TwiceDifferentiable reals function ->
  Iff
    (FunctionalEquation reals function)
    (Solution reals function)
