-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_b4:
-- a twice-differentiable real function with the stated endpoint and derivative
-- bounds has second derivative of magnitude at least 9/2 on [0, 1].
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1970B4 where

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

Predicate : Set -> Set1
Predicate A =
  A -> Set

whole : {A : Set} -> Predicate A
whole _ =
  Bottom -> Bottom

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

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals function domain point derivativeValue =
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
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt reals function point derivativeValue =
  DerivativeWithinAt
    reals
    function
    whole
    point
    derivativeValue

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

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

InClosedUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InClosedUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

InOpenUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InOpenUnitInterval reals x =
  StrictLess reals (zeroR reals) x
  and
  StrictLess reals x (oneR reals)

DifferentiableWithinOn :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Predicate R ->
  Set
DifferentiableWithinOn {R} reals function domain =
  (point : R) ->
  domain point ->
  Exists R
    (DerivativeWithinAt reals function domain point)

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

AbsoluteValueAtMost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteValueAtMost reals bound value =
  lessOrEqual reals (negate reals bound) value
  and
  lessOrEqual reals value bound

AbsoluteValueAtLeast :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteValueAtLeast reals bound value =
  lessOrEqual reals bound value
  or
  lessOrEqual reals value (negate reals bound)

threeHalves :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
threeHalves reals =
  divide reals
    (fromNat reals (suc (suc (suc zero))))
    (fromNat reals (suc (suc zero)))

nineHalves :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
nineHalves reals =
  divide reals
    (fromNat reals
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    (fromNat reals (suc (suc zero)))

module Putnam1970B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (calculus : StandardRealCalculus reals) where

  proposition : Set
  proposition =
    (x : R -> R) ->
    (DifferentiableOn reals x
      (InClosedUnitInterval reals)
    and
    DifferentiableOn reals
      (derivative calculus x)
      (InClosedUnitInterval reals)) ->
    subtract reals
      (x (oneR reals))
      (x (zeroR reals))
      ==
      oneR reals ->
    (derivative calculus x (zeroR reals) == zeroR reals
    and
    derivative calculus x (oneR reals) == zeroR reals) ->
    ((t : R) ->
      InOpenUnitInterval reals t ->
      AbsoluteValueAtMost reals
        (threeHalves reals)
        (derivative calculus x t)) ->
    Exists R
      (\ t ->
        InClosedUnitInterval reals t
        and
        AbsoluteValueAtLeast reals
          (nineHalves reals)
          (derivative calculus
            (derivative calculus x)
            t))

putnam-1970-b4 : Set1
putnam-1970-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  Putnam1970B4Statement.proposition reals calculus
