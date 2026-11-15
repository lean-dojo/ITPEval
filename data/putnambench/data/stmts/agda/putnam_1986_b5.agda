-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_b5:
-- the assertion that every real polynomial self-map preserving
-- x^2 + y^2 + z^2 + xyz is an even-sign permutation of the coordinates is false.
-- This file contains no proof.

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

record Monomial (R : Set) : Set where
  constructor monomial
  field
    coefficient : R
    xExponent   : Nat
    yExponent   : Nat
    zExponent   : Nat

open Monomial

Polynomial : Set -> Set
Polynomial R =
  List (Monomial R)

module Putnam1986B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  infix 4 _~=P_

  power : R -> Nat -> R
  power x zero =
    oneR reals
  power x (suc n) =
    multiply reals x (power x n)

  evaluateMonomial :
    Monomial R ->
    R ->
    R ->
    R ->
    R
  evaluateMonomial term x y z =
    multiply reals
      (coefficient term)
      (multiply reals
        (power x (xExponent term))
        (multiply reals
          (power y (yExponent term))
          (power z (zExponent term))))

  evaluate :
    Polynomial R ->
    R ->
    R ->
    R ->
    R
  evaluate [] x y z =
    zeroR reals
  evaluate (term ∷ terms) x y z =
    add reals
      (evaluateMonomial term x y z)
      (evaluate terms x y z)

  _~=P_ :
    Polynomial R ->
    Polynomial R ->
    Set
  p ~=P q =
    (x y z : R) ->
    evaluate p x y z == evaluate q x y z

  xCoordinate : Polynomial R
  xCoordinate =
    monomial (oneR reals) (suc zero) zero zero ∷ []

  yCoordinate : Polynomial R
  yCoordinate =
    monomial (oneR reals) zero (suc zero) zero ∷ []

  zCoordinate : Polynomial R
  zCoordinate =
    monomial (oneR reals) zero zero (suc zero) ∷ []

  negativeXCoordinate : Polynomial R
  negativeXCoordinate =
    monomial (negate reals (oneR reals)) (suc zero) zero zero ∷ []

  negativeYCoordinate : Polynomial R
  negativeYCoordinate =
    monomial (negate reals (oneR reals)) zero (suc zero) zero ∷ []

  negativeZCoordinate : Polynomial R
  negativeZCoordinate =
    monomial (negate reals (oneR reals)) zero zero (suc zero) ∷ []

  fValue : R -> R -> R -> R
  fValue x y z =
    add reals
      (multiply reals x x)
      (add reals
        (multiply reals y y)
        (add reals
          (multiply reals z z)
          (multiply reals (multiply reals x y) z)))

  PreservesF :
    Polynomial R ->
    Polynomial R ->
    Polynomial R ->
    Set
  PreservesF p q r =
    (x y z : R) ->
    fValue
      (evaluate p x y z)
      (evaluate q x y z)
      (evaluate r x y z)
    ==
    fValue x y z

  data IsPermutationOf
    (p q r a b c : Polynomial R) : Set where

    order-abc :
      p ~=P a ->
      q ~=P b ->
      r ~=P c ->
      IsPermutationOf p q r a b c

    order-acb :
      p ~=P a ->
      q ~=P c ->
      r ~=P b ->
      IsPermutationOf p q r a b c

    order-bac :
      p ~=P b ->
      q ~=P a ->
      r ~=P c ->
      IsPermutationOf p q r a b c

    order-bca :
      p ~=P b ->
      q ~=P c ->
      r ~=P a ->
      IsPermutationOf p q r a b c

    order-cab :
      p ~=P c ->
      q ~=P a ->
      r ~=P b ->
      IsPermutationOf p q r a b c

    order-cba :
      p ~=P c ->
      q ~=P b ->
      r ~=P a ->
      IsPermutationOf p q r a b c

  AllowedSignedCoordinatePermutation :
    Polynomial R ->
    Polynomial R ->
    Polynomial R ->
    Set
  AllowedSignedCoordinatePermutation p q r =
    IsPermutationOf
      p q r
      xCoordinate yCoordinate zCoordinate
    or
    IsPermutationOf
      p q r
      xCoordinate negativeYCoordinate negativeZCoordinate
    or
    IsPermutationOf
      p q r
      negativeXCoordinate yCoordinate negativeZCoordinate
    or
    IsPermutationOf
      p q r
      negativeXCoordinate negativeYCoordinate zCoordinate

  ClassificationClaim : Set
  ClassificationClaim =
    (p q r : Polynomial R) ->
    PreservesF p q r ->
    AllowedSignedCoordinatePermutation p q r

  solution : Set
  solution =
    Bottom

  proposition : Set
  proposition =
    Iff ClassificationClaim solution

putnam-1986-b5 : Set1
putnam-1986-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1986B5Statement.proposition reals
