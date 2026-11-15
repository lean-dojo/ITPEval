-- Statement-only formalization of PutnamBench corpus artifact putnam_1999_a1:
-- three real polynomials exist whose absolute-value combination equals the
-- specified piecewise-linear function on every real input. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
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

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Polynomial : Set -> Set
Polynomial R =
  List R

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals [] x =
  zeroR reals
evaluatePolynomial reals (coefficient ∷ coefficients) x =
  add reals
    coefficient
    (multiply reals x
      (evaluatePolynomial reals coefficients x))

module Putnam1999A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  negativeOne : R
  negativeOne =
    negate reals (oneR reals)

  two : R
  two =
    fromNat reals 2

  three : R
  three =
    fromNat reals 3

  leftHandSide :
    Polynomial R ->
    Polynomial R ->
    Polynomial R ->
    R ->
    R
  leftHandSide f g h x =
    add reals
      (subtract reals
        (absoluteValue reals (evaluatePolynomial reals f x))
        (absoluteValue reals (evaluatePolynomial reals g x)))
      (evaluatePolynomial reals h x)

  middleValue : R -> R
  middleValue x =
    add reals
      (multiply reals three x)
      two

  rightValue : R -> R
  rightValue x =
    add reals
      (multiply reals (negate reals two) x)
      two

  MatchesPiecewiseFunction :
    Polynomial R ->
    Polynomial R ->
    Polynomial R ->
    Set
  MatchesPiecewiseFunction f g h =
    (x : R) ->
    (StrictLess reals x negativeOne ->
      leftHandSide f g h x == negativeOne)
    and
    (((lessOrEqual reals negativeOne x
      and lessOrEqual reals x (zeroR reals)) ->
      leftHandSide f g h x == middleValue x)
    and
    (StrictLess reals (zeroR reals) x ->
      leftHandSide f g h x == rightValue x))

  proposition : Set
  proposition =
    Exists (Polynomial R)
      (\ f ->
        Exists (Polynomial R)
          (\ g ->
            Exists (Polynomial R)
              (\ h ->
                MatchesPiecewiseFunction f g h)))

putnam-1999-a1 : Set1
putnam-1999-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1999A1Statement.proposition reals
