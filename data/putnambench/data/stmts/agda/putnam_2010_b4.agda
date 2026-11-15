-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_b4
-- (putnambench__agda__putnam_2010_b4): classification of pairs of real
-- polynomials satisfying p(x)q(x+1) - p(x+1)q(x) = 1. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
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

Polynomial : Set -> Set
Polynomial R =
  List R

evaluate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluate reals [] x =
  zeroR reals
evaluate reals (coefficient ∷ coefficients) x =
  add reals
    coefficient
    (multiply reals x (evaluate reals coefficients x))

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

module Putnam2010B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (p q : Polynomial R) where

  affine : R -> R -> R -> R
  affine slope intercept x =
    add reals
      (multiply reals slope x)
      intercept

  FunctionalEquation : Set
  FunctionalEquation =
    (x : R) ->
    subtract reals
      (multiply reals
        (evaluate reals p x)
        (evaluate reals q (add reals x (oneR reals))))
      (multiply reals
        (evaluate reals p (add reals x (oneR reals)))
        (evaluate reals q x))
    ==
    oneR reals

  Solution : Set
  Solution =
    Exists R
      (\ a ->
        Exists R
          (\ b ->
            Exists R
              (\ c ->
                Exists R
                  (\ d ->
                    subtract reals
                      (multiply reals b c)
                      (multiply reals a d)
                    ==
                    oneR reals
                    and
                    ((x : R) ->
                      evaluate reals p x == affine a b x)
                    and
                    ((x : R) ->
                      evaluate reals q x == affine c d x)))))

  proposition : Set
  proposition =
    FunctionalEquation iff Solution

putnam-2010-b4 : Set1
putnam-2010-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (p q : Polynomial R) ->
  Putnam2010B4Statement.proposition reals p q
