-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_b4:
-- the positive fixed point of x = 2207 - 1 / x has eighth root
-- (3 + sqrt 5) / 2. This file contains no proof.

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

record StandardSquareAndEighthRoots
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    squareRoot eighthRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals
        (zeroR reals)
        (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      naturalPower reals (squareRoot x) 2 == x
    square-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) y ->
      naturalPower reals y 2 == x ->
      y == squareRoot x

    eighth-root-nonnegative :
      (x : R) ->
      lessOrEqual reals
        (zeroR reals)
        (eighthRoot x)
    eighth-root-power :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      naturalPower reals (eighthRoot x) 8 == x
    eighth-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) y ->
      naturalPower reals y 8 == x ->
      y == eighthRoot x

open StandardSquareAndEighthRoots

module Putnam1995B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardSquareAndEighthRoots reals) where

  one two three five twentyTwoOhSeven : R
  one =
    fromNat reals 1
  two =
    fromNat reals 2
  three =
    fromNat reals 3
  five =
    fromNat reals 5
  twentyTwoOhSeven =
    fromNat reals 2207

  solution : R
  solution =
    divide reals
      (add reals
        three
        (squareRoot roots five))
      two

  proposition : Set
  proposition =
    (contfrac : R) ->
    contfrac ==
      subtract reals
        twentyTwoOhSeven
        (divide reals one contfrac) ->
    StrictLess reals one contfrac ->
    eighthRoot roots contfrac == solution

putnam-1995-b4 : Set1
putnam-1995-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardSquareAndEighthRoots reals) ->
  Putnam1995B4Statement.proposition reals roots
