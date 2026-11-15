-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_a2:
-- a real quadratic form with negative discriminant, perturbed by arbitrary
-- cubic terms, has no nonzero zero sufficiently near the origin.
-- This file contains no proof.

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
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  addR reals x (negateR reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiplyR reals x x

cube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
cube reals x =
  multiplyR reals (square reals x) x

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  addR reals (oneR reals) (oneR reals)

four :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
four reals =
  addR reals (two reals) (two reals)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

discriminant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  R
discriminant reals A B C =
  subtract reals
    (square reals B)
    (multiplyR reals
      (four reals)
      (multiplyR reals A C))

squaredRadius :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
squaredRadius reals x y =
  addR reals (square reals x) (square reals y)

polynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R
polynomial reals A B C D E F G x y =
  addR reals
    (addR reals
      (addR reals
        (addR reals
          (multiplyR reals A (square reals x))
          (multiplyR reals
            (multiplyR reals B x)
            y))
        (multiplyR reals C (square reals y)))
      (multiplyR reals D (cube reals x)))
    (addR reals
      (addR reals
        (multiplyR reals
          (multiplyR reals E (square reals x))
          y)
        (multiplyR reals
          (multiplyR reals F x)
          (square reals y)))
      (multiplyR reals G (cube reals y)))

module Putnam1970A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (A B C D E F G : R) ->
    StrictLess reals
      (discriminant reals A B C)
      (zeroR reals) ->
    Exists R
      (\ delta ->
        StrictLess reals (zeroR reals) delta
        and
        Not
          (Exists R
            (\ x ->
              Exists R
                (\ y ->
                  StrictLess reals
                    (zeroR reals)
                    (squaredRadius reals x y)
                  and
                  StrictLess reals
                    (squaredRadius reals x y)
                    (square reals delta)
                  and
                  polynomial reals A B C D E F G x y
                    ==
                  zeroR reals))))

putnam-1970-a2 : Set1
putnam-1970-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1970A2Statement.proposition reals
