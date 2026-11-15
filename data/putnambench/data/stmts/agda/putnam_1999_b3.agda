-- Statement-only formalization of PutnamBench corpus artifact putnam_1999_b3
-- (putnambench__agda__putnam_1999_b3): a two-variable limit involving an
-- iterated power series over positive integer pairs with bounded ratio is 3.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true; false)
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
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
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

threeN : Nat
threeN =
  suc twoN

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

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

Positive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

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

lessEqualBool : Nat -> Nat -> Bool
lessEqualBool zero n =
  true
lessEqualBool (suc m) zero =
  false
lessEqualBool (suc m) (suc n) =
  lessEqualBool m n

andBool : Bool -> Bool -> Bool
andBool true b =
  b
andBool false b =
  false

ifBool :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
ifBool true whenTrue whenFalse =
  whenTrue
ifBool false whenTrue whenFalse =
  whenFalse

admissibleIndex : Nat -> Nat -> Bool
admissibleIndex m n =
  andBool
    (lessEqualBool oneN m)
    (andBool
      (lessEqualBool oneN n)
      (andBool
        (lessEqualBool n (twoN * m))
        (lessEqualBool m (twoN * n))))

putnamTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Nat ->
  Nat ->
  R
putnamTerm reals x y m n =
  ifBool
    (admissibleIndex m n)
    (multiply reals
      (naturalPower reals x m)
      (naturalPower reals y n))
    (zeroR reals)

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
  Positive reals epsilon ->
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
SeriesHasSum reals terms total =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    total

TotalSeriesValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
TotalSeriesValue {R} reals terms value =
  SeriesHasSum reals terms value
  or
  (Not
    (Exists R
      (\ candidate ->
        SeriesHasSum reals terms candidate))
  and
  value == zeroR reals)

IteratedTotalSeriesValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> Nat -> R) ->
  R ->
  Set
IteratedTotalSeriesValue {R} reals terms total =
  Exists (Nat -> R)
    (\ innerValues ->
      ((m : Nat) ->
        TotalSeriesValue reals
          (terms m)
          (innerValues m))
      and
      TotalSeriesValue reals innerValues total)

UnitSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
UnitSquare reals x y =
  lessOrEqual reals (zeroR reals) x
  and
  StrictLess reals x (oneR reals)
  and
  lessOrEqual reals (zeroR reals) y
  and
  StrictLess reals y (oneR reals)

limitExpression :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R -> R) ->
  R ->
  R ->
  R
limitExpression reals S x y =
  multiply reals
    (multiply reals
      (subtract reals
        (oneR reals)
        (multiply reals
          x
          (naturalPower reals y twoN)))
      (subtract reals
        (oneR reals)
        (multiply reals
          (naturalPower reals x twoN)
          y)))
    (S x y)

LimitWithinUnitSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R -> R) ->
  R ->
  Set
LimitWithinUnitSquare {R} reals function limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((x y : R) ->
        UnitSquare reals x y ->
        CloseTo reals (oneR reals) delta x ->
        CloseTo reals (oneR reals) delta y ->
        CloseTo reals limit epsilon (function x y)))

putnam-1999-b3 : Set1
putnam-1999-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (S : R -> R -> R) ->
  ((x y : R) ->
    IteratedTotalSeriesValue reals
      (putnamTerm reals x y)
      (S x y)) ->
  LimitWithinUnitSquare reals
    (limitExpression reals S)
    (fromNat reals threeN)
