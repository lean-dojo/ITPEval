-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_b6:
-- a real function whose partial derivatives exist at every interior disk point
-- and whose absolute value is at most one on the closed unit disk has an
-- interior point where the sum of the squared partial derivatives is at most
-- sixteen. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1967B6 where

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
  (point : R) ->
  Exists R (DerivativeAt reals function point)

PartiallyDifferentiableOn :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R -> R) ->
  (R -> R -> Set) ->
  Set
PartiallyDifferentiableOn {R} reals f domain =
  ((x y : R) ->
    domain x y ->
    Exists R (DerivativeAt reals (\ t -> f t y) x))
  and
  ((x y : R) ->
    domain x y ->
    Exists R (DerivativeAt reals (f x) y))

UnitDisk :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
UnitDisk reals x y =
  lessOrEqual reals
    (add reals (square reals x) (square reals y))
    (oneR reals)

InteriorUnitDisk :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
InteriorUnitDisk reals x y =
  StrictLess reals
    (add reals (square reals x) (square reals y))
    (oneR reals)

BoundedByOne :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
BoundedByOne reals value =
  lessOrEqual reals (negate reals (oneR reals)) value
  and
  lessOrEqual reals value (oneR reals)

fourN : Nat
fourN =
  suc (suc (suc (suc zero)))

eightN : Nat
eightN =
  fourN + fourN

sixteenN : Nat
sixteenN =
  eightN + eightN

module Putnam1967B6Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  GradientBoundAt :
    (R -> R -> R) ->
    R ->
    R ->
    Set
  GradientBoundAt f x y =
    Exists R
      (\ partialX ->
        Exists R
          (\ partialY ->
            DerivativeAt reals
              (\ t -> f t y)
              x
              partialX
            and
            DerivativeAt reals
              (f x)
              y
              partialY
            and
            lessOrEqual reals
              (add reals
                (square reals partialX)
                (square reals partialY))
              (fromNat reals sixteenN)))

  proposition : Set
  proposition =
    (f : R -> R -> R) ->
    PartiallyDifferentiableOn reals f
      (InteriorUnitDisk reals) ->
    ((x y : R) ->
      UnitDisk reals x y ->
      BoundedByOne reals (f x y)) ->
    Exists R
      (\ x0 ->
        Exists R
          (\ y0 ->
            InteriorUnitDisk reals x0 y0
            and
            GradientBoundAt f x0 y0))

putnam-1967-b6 : Set1
putnam-1967-b6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1967B6Statement.proposition reals
