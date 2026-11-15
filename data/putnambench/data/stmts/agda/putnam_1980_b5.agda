-- Statement-only formalization of PutnamBench corpus artifact putnam_1980_b5:
-- the nonnegative parameters for which a class of increasing, convex,
-- continuous functions on [0,1] is closed under multiplication. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

Predicate : Set -> Set1
Predicate A =
  A -> Set

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
      (P : Predicate R) ->
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

ClosedUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate R
ClosedUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

ContinuousWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
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
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  Set
ContinuousOn {R} reals function domain =
  (x : R) ->
  domain x ->
  ContinuousWithinAt reals function domain x

StrictlyIncreasingOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  Set
StrictlyIncreasingOn {R} reals function domain =
  (x y : R) ->
  domain x ->
  domain y ->
  StrictLess reals x y ->
  StrictLess reals (function x) (function y)

ConvexOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  Set
ConvexOn {R} reals function domain =
  (u v s : R) ->
  domain u ->
  domain v ->
  domain s ->
  lessOrEqual reals
    (function
      (add reals
        (multiply reals s u)
        (multiply reals
          (subtract reals (oneR reals) s)
          v)))
    (add reals
      (multiply reals s (function u))
      (multiply reals
        (subtract reals (oneR reals) s)
        (function v)))

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

module Putnam1980B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  oneThird : R
  oneThird =
    divide reals
      (oneR reals)
      (fromNat reals threeN)

  twoThirds : R
  twoThirds =
    divide reals
      (fromNat reals twoN)
      (fromNat reals threeN)

  DifferenceCondition :
    R ->
    (R -> R) ->
    Set
  DifferenceCondition t f =
    lessOrEqual reals
      (multiply reals
        t
        (add reals
          (subtract reals
            (f twoThirds)
            (multiply reals
              (fromNat reals twoN)
              (f oneThird)))
          (f (zeroR reals))))
      (add reals
        (subtract reals
          (f (oneR reals))
          (multiply reals
            (fromNat reals twoN)
            (f twoThirds)))
        (f oneThird))

  Qualifies :
    R ->
    (R -> R) ->
    Set
  Qualifies t f =
    ((x : R) ->
      ClosedUnitInterval reals x ->
      lessOrEqual reals (zeroR reals) (f x))
    and
    StrictlyIncreasingOn reals f (ClosedUnitInterval reals)
    and
    ConvexOn reals f (ClosedUnitInterval reals)
    and
    ContinuousOn reals f (ClosedUnitInterval reals)
    and
    DifferenceCondition t f

  ClosedUnderMultiplication :
    R ->
    Set
  ClosedUnderMultiplication t =
    (f g : R -> R) ->
    Qualifies t f ->
    Qualifies t g ->
    Qualifies t
      (\ x -> multiply reals (f x) (g x))

  solution :
    R ->
    Set
  solution t =
    lessOrEqual reals t (oneR reals)

  proposition : Set
  proposition =
    (t : R) ->
    lessOrEqual reals (zeroR reals) t ->
    Iff
      (ClosedUnderMultiplication t)
      (solution t)

putnam-1980-b5 : Set1
putnam-1980-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1980B5Statement.proposition reals
