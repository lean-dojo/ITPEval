-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_b2
-- (putnambench__agda__putnam_2001_b2): the real solutions of a system of two
-- rational polynomial equations form a specified singleton. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  twoN + twoN

fiveN : Nat
fiveN =
  suc fourN

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

module Putnam2001B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  equationOne :
    R ->
    R ->
    Set
  equationOne x y =
    add reals
      (divide reals (oneR reals) x)
      (divide reals
        (oneR reals)
        (multiply reals (fromNat reals twoN) y))
    ==
    multiply reals
      (add reals
        (naturalPower reals x twoN)
        (multiply reals
          (fromNat reals threeN)
          (naturalPower reals y twoN)))
      (add reals
        (multiply reals
          (fromNat reals threeN)
          (naturalPower reals x twoN))
        (naturalPower reals y twoN))

  equationTwo :
    R ->
    R ->
    Set
  equationTwo x y =
    subtract reals
      (divide reals (oneR reals) x)
      (divide reals
        (oneR reals)
        (multiply reals (fromNat reals twoN) y))
    ==
    multiply reals
      (fromNat reals twoN)
      (subtract reals
        (naturalPower reals y fourN)
        (naturalPower reals x fourN))

  isPositiveFifthRootOfThree :
    R ->
    Set
  isPositiveFifthRootOfThree root =
    StrictLess reals (zeroR reals) root
    and
    naturalPower reals root fiveN == fromNat reals threeN

  isSolutionPair :
    R ->
    R ->
    Set
  isSolutionPair x y =
    Exists R
      (\ root ->
        isPositiveFifthRootOfThree root
        and
        (x ==
          divide reals
            (add reals root (oneR reals))
            (fromNat reals twoN)
        and
        y ==
          divide reals
            (subtract reals root (oneR reals))
            (fromNat reals twoN)))

  proposition : Set
  proposition =
    (x y : R) ->
    x != zeroR reals ->
    y != zeroR reals ->
    (equationOne x y and equationTwo x y)
      iff
    isSolutionPair x y

putnam-2001-b2 : Set1
putnam-2001-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2001B2Statement.proposition reals
