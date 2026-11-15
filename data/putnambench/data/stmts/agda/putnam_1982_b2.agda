-- Statement-only formalization of PutnamBench corpus artifact putnam_1982_b2:
-- the Gaussian-weighted double integral of the number of integer lattice
-- points in a centered disk equals pi times (2g - 1)^2, where g is the
-- Gaussian series over the natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

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

record Pair (A B : Set) : Set where
  constructor pair
  field
    firstOf  : A
    secondOf : B

open Pair

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

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

integerToReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
integerToReal reals (pos n) =
  fromNat reals n
integerToReal reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

record PiValue
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (value : R) :
  Set where

  field
    positive :
      StrictLess reals (zeroR reals) value
    leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals value (fromNat reals fourN))

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential : R -> R
    pi : R

    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)

    pi-value :
      PiValue reals pi

open StandardRealAnalysis

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
    halfStep =
      divide reals
        step
        (fromNat reals twoN)
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
              halfStep)))
        step)

IntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
IntervalIntegralValue reals lower upper function value =
  ConvergesTo reals
    (\ n ->
      midpointRiemannSum reals
        lower
        upper
        function
        (suc n))
    value

WholeLineIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
WholeLineIntegralValue {R} reals function value =
  Exists (Nat -> R)
    (\ partialIntegrals ->
      ((n : Nat) ->
        IntervalIntegralValue reals
          (negate reals (fromNat reals n))
          (fromNat reals n)
          function
          (partialIntegrals n))
      and
      ConvergesTo reals partialIntegrals value)

record IteratedWholeLineIntegralValue
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R -> R)
  (value : R) :
  Set where

  field
    innerValues :
      R ->
      R
    inner-integrals :
      (y : R) ->
      WholeLineIntegralValue reals
        (\ x -> function x y)
        (innerValues y)
    outer-integral :
      WholeLineIntegralValue reals
        innerValues
        value

LatticePointCount :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R -> Nat) ->
  Set
LatticePointCount {R} reals A =
  (x y : R) ->
  HasCardinality
    (\ latticePoint ->
      lessOrEqual reals
        (add reals
          (square reals
            (integerToReal reals (firstOf latticePoint)))
          (square reals
            (integerToReal reals (secondOf latticePoint))))
        (add reals
          (square reals x)
          (square reals y)))
    (A x y)

module Putnam1982B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardRealAnalysis reals)
  (A : R -> R -> Nat) where

  gaussianSeriesTerm :
    Nat ->
    R
  gaussianSeriesTerm n =
    exponential analysis
      (negate reals
        (square reals (fromNat reals n)))

  integrand :
    R ->
    R ->
    R
  integrand x y =
    multiply reals
      (fromNat reals (A x y))
      (exponential analysis
        (negate reals
          (add reals
            (square reals x)
            (square reals y))))

  solution :
    R ->
    R
  solution g =
    multiply reals
      (pi analysis)
      (square reals
        (subtract reals
          (multiply reals
            (fromNat reals twoN)
            g)
          (oneR reals)))

putnam-1982-b2 : Set1
putnam-1982-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  (A : R -> R -> Nat) ->
  (g I : R) ->
  LatticePointCount reals A ->
  SeriesHasSum reals
    (Putnam1982B2Statement.gaussianSeriesTerm reals analysis A)
    g ->
  IteratedWholeLineIntegralValue reals
    (Putnam1982B2Statement.integrand reals analysis A)
    I ->
  I ==
  Putnam1982B2Statement.solution reals analysis A g
