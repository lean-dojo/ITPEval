-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_b6:
-- the expected right-endpoint Riemann sum over the ordered unit simplex is a
-- unit-interval integral against a bounded polynomial of degree n. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam1989B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Between :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
Between reals lower upper x =
  lessOrEqual reals lower x
  and
  lessOrEqual reals x upper

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

ContinuousOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Set
ContinuousOn {R} reals lower upper function =
  (x : R) ->
  Between reals lower upper x ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((y : R) ->
        Between reals lower upper y ->
        CloseTo reals x delta y ->
        CloseTo reals (function x) epsilon (function y)))

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

twoN : Nat
twoN =
  suc (suc zero)

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector : Set -> Nat -> Set
Vector A n =
  Fin n -> A

emptyVector :
  {A : Set} ->
  Vector A zero
emptyVector ()

castSucc :
  {n : Nat} ->
  Fin n ->
  Fin (suc n)
castSucc fzero =
  fzero
castSucc (fsuc i) =
  fsuc (castSucc i)

snoc :
  {A : Set} ->
  {n : Nat} ->
  Vector A n ->
  A ->
  Vector A (suc n)
snoc {n = zero} vector last fzero =
  last
snoc {n = suc n} vector last fzero =
  vector fzero
snoc {n = suc n} vector last (fsuc i) =
  snoc
    (\ j -> vector (fsuc j))
    last
    i

extendedCoordinate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Vector R n ->
  Fin (suc (suc n)) ->
  R
extendedCoordinate reals {zero} vector fzero =
  zeroR reals
extendedCoordinate reals {zero} vector (fsuc fzero) =
  oneR reals
extendedCoordinate reals {suc n} vector fzero =
  zeroR reals
extendedCoordinate reals {suc n} vector (fsuc fzero) =
  vector fzero
extendedCoordinate reals {suc n} vector (fsuc (fsuc i)) =
  extendedCoordinate reals
    (\ j -> vector (fsuc j))
    (fsuc i)

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  add reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

rightEndpointSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (R -> R) ->
  Vector R n ->
  R
rightEndpointSum reals {n} function point =
  sumFin reals
    (\ i ->
      let
        leftEndpoint =
          extendedCoordinate reals point (castSucc i)
        rightEndpoint =
          extendedCoordinate reals point (fsuc i)
      in
      multiply reals
        (subtract reals rightEndpoint leftEndpoint)
        (function rightEndpoint))

data OrderedSimplexIntegralValue
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  {n : Nat} ->
  R ->
  (Vector R n -> R) ->
  R ->
  Set where

  zero-dimensional :
    {upper : R} ->
    {function : Vector R zero -> R} ->
    {value : R} ->
    function emptyVector == value ->
    OrderedSimplexIntegralValue reals
      upper function value

  successor-dimensional :
    {n : Nat} ->
    {upper : R} ->
    {function : Vector R (suc n) -> R} ->
    {value : R} ->
    (innerValues : R -> R) ->
    ((t : R) ->
      Between reals (zeroR reals) upper t ->
      OrderedSimplexIntegralValue reals
        t
        (\ point -> function (snoc point t))
        (innerValues t)) ->
    IntervalIntegralValue reals
      (zeroR reals)
      upper
      innerValues
      value ->
    OrderedSimplexIntegralValue reals
      upper function value

record Polynomial (R : Set) : Set where
  constructor polynomial
  field
    coefficient : Nat -> R
    cutoff : Nat

open Polynomial

PolynomialRepresentation :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Set
PolynomialRepresentation reals P =
  (k : Nat) ->
  cutoff P <N k ->
  coefficient P k == zeroR reals

HasDegree :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  Set
HasDegree reals P n =
  coefficient P n != zeroR reals
  and
  ((k : Nat) ->
    n <N k ->
    coefficient P k == zeroR reals)

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals P x =
  sumFirst reals
    (suc (cutoff P))
    (\ k ->
      multiply reals
        (coefficient P k)
        (naturalPower reals x k))

BoundedOnUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Set
BoundedOnUnitInterval {R} reals P =
  (t : R) ->
  Between reals (zeroR reals) (oneR reals) t ->
  Between reals
    (zeroR reals)
    (oneR reals)
    (evaluatePolynomial reals P t)

module Putnam1989B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (n : Nat) where

  constantOne :
    Vector R n ->
    R
  constantOne _ =
    oneR reals

  weightedIntegrand :
    (R -> R) ->
    Polynomial R ->
    R ->
    R
  weightedIntegrand function P t =
    multiply reals
      (function t)
      (evaluatePolynomial reals P t)

  proposition : Set
  proposition =
    n != zero ->
    Exists (Polynomial R)
      (\ P ->
        PolynomialRepresentation reals P
        and
        (HasDegree reals P n
        and
        (BoundedOnUnitInterval reals P
        and
        Exists R
          (\ simplexVolume ->
            OrderedSimplexIntegralValue reals
              (oneR reals)
              constantOne
              simplexVolume
            and
            ((function : R -> R) ->
              function (oneR reals) == zeroR reals ->
              ContinuousOn reals
                (zeroR reals)
                (oneR reals)
                function ->
              Exists R
                (\ sumIntegral ->
                  OrderedSimplexIntegralValue reals
                    (oneR reals)
                    (rightEndpointSum reals {n = n} function)
                    sumIntegral
                  and
                  Exists R
                    (\ weightedIntegral ->
                      IntervalIntegralValue reals
                        (zeroR reals)
                        (oneR reals)
                        (weightedIntegrand function P)
                        weightedIntegral
                      and
                      divide reals
                        sumIntegral
                        simplexVolume
                      == weightedIntegral)))))))

putnam-1989-b6 : Set1
putnam-1989-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Putnam1989B6Statement.proposition reals n
