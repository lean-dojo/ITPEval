-- Statement-only formalization of PutnamBench corpus artifact putnam_1963_a3:
-- the zero-initial-data solution of a factored Euler differential equation is
-- represented by an explicit integral kernel. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1963A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n = suc m <=N n

oneN : Nat
oneN = suc zero

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

factorial : Nat -> Nat
factorial zero = oneN
factorial (suc n) = suc n * factorial n

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

Predicate : Set -> Set1
Predicate A = A -> Set

ContinuousWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Predicate R ->
  R ->
  Set
ContinuousWithinAt {R} reals function domain point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        domain x ->
        CloseTo reals point delta x ->
        CloseTo reals (function point) epsilon (function x)))

ContinuousOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Predicate R ->
  Set
ContinuousOn {R} reals function domain =
  (x : R) ->
  domain x ->
  ContinuousWithinAt reals function domain x

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

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Predicate R ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals function domain point derivative =
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
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

whole : {A : Set} -> Predicate A
whole _ = Bottom -> Bottom

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt reals function point derivative =
  DerivativeWithinAt reals function whole point derivative

record StandardCalculus
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    derivative : (R -> R) -> R -> R
    derivative-correct :
      (function : R -> R) ->
      (point value : R) ->
      DerivativeAt reals function point value ->
      derivative function point == value
    derivative-totalized-at-zero :
      (function : R -> R) ->
      (point : R) ->
      Not (Exists R (DerivativeAt reals function point)) ->
      derivative function point == zeroR reals

open StandardCalculus

iteratedDerivative :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardCalculus reals ->
  Nat ->
  (R -> R) ->
  R ->
  R
iteratedDerivative calculus zero function =
  function
iteratedDerivative calculus (suc n) function =
  derivative calculus (iteratedDerivative calculus n function)

OpenNeighborhood :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
OpenNeighborhood reals center radius x =
  CloseTo reals center radius x

ClosedFromOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R
ClosedFromOne reals x =
  lessOrEqual reals (oneR reals) x

ContDiffOn :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardCalculus reals ->
  Nat ->
  (R -> R) ->
  Predicate R ->
  Set
ContDiffOn {R} reals calculus n function domain =
  ((k : Nat) ->
    k <N n ->
    (x : R) ->
    domain x ->
    DerivativeWithinAt reals
      (iteratedDerivative calculus k function)
      domain
      x
      (iteratedDerivative calculus (suc k) function x))
  and
  ((k : Nat) ->
    k <=N n ->
    ContinuousOn reals
      (iteratedDerivative calculus k function)
      domain)

ContDiffAt :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardCalculus reals ->
  Nat ->
  (R -> R) ->
  R ->
  Set
ContDiffAt reals calculus n function point =
  Exists _
    (\ radius ->
      StrictLess reals (zeroR reals) radius
      and
      ContDiffOn reals calculus n function
        (OpenNeighborhood reals point radius))

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

riemannStep :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Nat ->
  R
riemannStep reals lower upper pieces =
  divide reals
    (subtract reals upper lower)
    (fromNat reals pieces)

rightRiemannSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  (R -> R) ->
  Nat ->
  R
rightRiemannSum reals lower upper function pieces =
  let
    step = riemannStep reals lower upper pieces
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (add reals lower
            (multiply reals
              (fromNat reals (suc i))
              step)))
        step)

IntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
IntervalIntegralValue reals lower upper function value =
  SequentialLimit reals
    (\ n ->
      rightRiemannSum reals lower upper function (suc n))
    value

module Putnam1963A3Statement
  {R : Set}
  (reals : CompleteOrderedField R)
  (calculus : StandardCalculus reals) where

  solutionKernel :
    (R -> R) ->
    Nat ->
    R ->
    R ->
    R
  solutionKernel f n x t =
    divide reals
      (multiply reals
        (naturalPower reals
          (subtract reals x t)
          (pred n))
        (f t))
      (multiply reals
        (fromNat reals (factorial (pred n)))
        (naturalPower reals t n))

  operatorFactor :
    Nat ->
    (R -> R) ->
    R ->
    R
  operatorFactor i function x =
    subtract reals
      (multiply reals x (derivative calculus function x))
      (multiply reals (fromNat reals i) (function x))

  OperatorRecurrence :
    (Nat -> (R -> R) -> (R -> R)) ->
    Set
  OperatorRecurrence P =
    ((function : R -> R) ->
      (x : R) ->
      P zero function x == function x)
    and
    ((i : Nat) ->
      (function : R -> R) ->
      (x : R) ->
      P (suc i) function x ==
      P i (operatorFactor i function) x)

  EqOnFromOne :
    (R -> R) ->
    (R -> R) ->
    Set
  EqOnFromOne leftFunction rightFunction =
    (x : R) ->
    ClosedFromOne reals x ->
    leftFunction x == rightFunction x

  proposition : Set
  proposition =
    (P : Nat -> (R -> R) -> (R -> R)) ->
    OperatorRecurrence P ->
    (n : Nat) ->
    zero <N n ->
    (f y : R -> R) ->
    ContinuousOn reals f (ClosedFromOne reals) ->
    ContDiffOn reals calculus n y (ClosedFromOne reals) ->
    ContDiffAt reals calculus n y (oneR reals) ->
    Iff
      (((i : Nat) ->
        i <N n ->
        iteratedDerivative calculus i y (oneR reals) ==
        zeroR reals)
      and
      EqOnFromOne (P n y) f)
      ((x : R) ->
        ClosedFromOne reals x ->
        IntervalIntegralValue reals
          (oneR reals)
          x
          (solutionKernel f n x)
          (y x))

putnam-1963-a3 : Set1
putnam-1963-a3 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (calculus : StandardCalculus reals) ->
  Putnam1963A3Statement.proposition reals calculus
