-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_a2:
-- the local explicit solution for the first component of a differentiable
-- real-valued system of three nonlinear differential equations. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009A2 where

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
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN + twoN

sixN : Nat
sixN =
  twoN + fourN

twelveN : Nat
twelveN =
  sixN + sixN

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

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
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
    (\ n -> sumFirst reals n terms)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals
    (negate reals (oneR reals))
    n

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

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (suc (twoN * n))))
    (fromNat reals (factorial (suc (twoN * n))))

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (twoN * n)))
    (fromNat reals (factorial (twoN * n)))

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

record StandardRealElementaryFunctions
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm sine cosine : R -> R
    pi : R

    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)

    exponential-positive :
      (x : R) ->
      StrictLess reals
        (zeroR reals)
        (exponential x)

    exponential-injective :
      (x y : R) ->
      exponential x == exponential y ->
      x == y

    exponential-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (logarithm x) == x

    sine-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)

    cosine-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi

    pi-leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals pi (fromNat reals fourN))

open StandardRealElementaryFunctions

Predicate : Set -> Set1
Predicate A =
  A -> Set

whole : {A : Set} -> Predicate A
whole _ =
  Bottom -> Bottom

OpenInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Predicate R
OpenInterval reals lower upper x =
  StrictLess reals lower x
  and
  StrictLess reals x upper

differenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
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
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    derivative : (R -> R) -> R -> R

    derivative-correct :
      (function : R -> R) ->
      (point derivativeValue : R) ->
      DerivativeAt reals function point derivativeValue ->
      derivative function point == derivativeValue

    derivative-totalized-at-zero :
      (function : R -> R) ->
      (point : R) ->
      Not (Exists R (DerivativeAt reals function point)) ->
      derivative function point == zeroR reals

open StandardRealCalculus

DifferentiableOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  Set
DifferentiableOn {R} reals function domain =
  (point : R) ->
  domain point ->
  Exists R
    (DerivativeAt reals function point)

realPower :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardRealElementaryFunctions reals ->
  R ->
  R ->
  R
realPower {reals = reals} elementary base exponent =
  exponential elementary
    (multiply reals exponent (logarithm elementary base))

module Putnam2009A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (elementary : StandardRealElementaryFunctions reals)
  (calculus : StandardRealCalculus reals) where

  oneSixth : R
  oneSixth =
    divide reals
      (oneR reals)
      (fromNat reals sixN)

  minusOneTwelfth : R
  minusOneTwelfth =
    negate reals
      (divide reals
        (oneR reals)
        (fromNat reals twelveN))

  angle : R -> R
  angle x =
    add reals
      (multiply reals (fromNat reals sixN) x)
      (divide reals
        (pi elementary)
        (fromNat reals fourN))

  solution : R -> R
  solution x =
    multiply reals
      (realPower elementary
        (fromNat reals twoN)
        minusOneTwelfth)
      (realPower elementary
        (divide reals
          (sine elementary (angle x))
          (naturalPower reals
            (cosine elementary (angle x))
            twoN))
        oneSixth)

  firstEquation :
    (R -> R) ->
    (R -> R) ->
    (R -> R) ->
    R ->
    R
  firstEquation f g h x =
    add reals
      (multiply reals
        (multiply reals
          (multiply reals
            (fromNat reals twoN)
            (naturalPower reals (f x) twoN))
          (g x))
        (h x))
      (divide reals
        (oneR reals)
        (multiply reals (g x) (h x)))

  secondEquation :
    (R -> R) ->
    (R -> R) ->
    (R -> R) ->
    R ->
    R
  secondEquation f g h x =
    add reals
      (multiply reals
        (multiply reals
          (f x)
          (naturalPower reals (g x) twoN))
        (h x))
      (divide reals
        (fromNat reals fourN)
        (multiply reals (f x) (h x)))

  thirdEquation :
    (R -> R) ->
    (R -> R) ->
    (R -> R) ->
    R ->
    R
  thirdEquation f g h x =
    add reals
      (multiply reals
        (multiply reals
          (multiply reals
            (fromNat reals (suc twoN))
            (f x))
          (g x))
        (naturalPower reals (h x) twoN))
      (divide reals
        (oneR reals)
        (multiply reals (f x) (g x)))

  proposition : Set
  proposition =
    (f g h : R -> R) ->
    (a b : R) ->
    OpenInterval reals a b (zeroR reals) ->
    (DifferentiableOn reals f (OpenInterval reals a b)
    and
    DifferentiableOn reals g (OpenInterval reals a b)
    and
    DifferentiableOn reals h (OpenInterval reals a b)) ->
    (((x : R) ->
      OpenInterval reals a b x ->
      derivative calculus f x == firstEquation f g h x)
    and
    f (zeroR reals) == oneR reals) ->
    (((x : R) ->
      OpenInterval reals a b x ->
      derivative calculus g x == secondEquation f g h x)
    and
    g (zeroR reals) == oneR reals) ->
    (((x : R) ->
      OpenInterval reals a b x ->
      derivative calculus h x == thirdEquation f g h x)
    and
    h (zeroR reals) == oneR reals) ->
    Exists R
      (\ c ->
        Exists R
          (\ d ->
            OpenInterval reals c d (zeroR reals)
            and
            ((x : R) ->
              OpenInterval reals c d x ->
              f x == solution x)))

putnam-2009-a2 : Set1
putnam-2009-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (elementary : StandardRealElementaryFunctions reals) ->
  (calculus : StandardRealCalculus reals) ->
  Putnam2009A2Statement.proposition
    reals
    elementary
    calculus
