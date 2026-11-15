-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a2:
-- no positive continuous real function on [0,1] can have total integral one
-- and first and second moments alpha and alpha squared. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1964A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

Predicate : Set -> Set1
Predicate A = A -> Set

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
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : Predicate R) ->
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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

ClosedUnitInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R
ClosedUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

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
SequentialLimit reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

rightRiemannSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Nat ->
  R
rightRiemannSum reals function pieces =
  let
    step = divide reals (oneR reals) (fromNat reals pieces)
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (multiply reals
            (fromNat reals (suc i))
            step))
        step)

UnitIntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
UnitIntervalIntegralValue reals function value =
  SequentialLimit reals
    (\ n -> rightRiemannSum reals function (suc n))
    value

module Putnam1964A2Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  Qualifies :
    R ->
    (R -> R) ->
    Set
  Qualifies alpha f =
    ((x : R) ->
      ClosedUnitInterval reals x ->
      StrictLess reals (zeroR reals) (f x))
    and
    ContinuousOn reals f (ClosedUnitInterval reals)
    and
    UnitIntervalIntegralValue reals f (oneR reals)
    and
    UnitIntervalIntegralValue reals
      (\ x -> multiply reals x (f x))
      alpha
    and
    UnitIntervalIntegralValue reals
      (\ x -> multiply reals (square reals x) (f x))
      (square reals alpha)

  proposition : Set
  proposition =
    (alpha : R) ->
    (f : R -> R) ->
    Iff Bottom (Qualifies alpha f)

putnam-1964-a2 : Set1
putnam-1964-a2 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964A2Statement.proposition reals
