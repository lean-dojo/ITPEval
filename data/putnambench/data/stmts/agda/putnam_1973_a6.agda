-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_a6:
-- seven distinct real affine lines cannot have at least six points incident
-- to exactly three lines and four points incident to exactly two lines.
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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

seven : Nat
seven =
  suc six

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

open CompleteOrderedField

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

record Line (R : Set) : Set where
  constructor line
  field
    slope     : R
    intercept : R

open Point
open Line

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective function =
  (i j : _) ->
  function i == function j ->
  i == j

module Putnam1973A6Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  LineIndex : Set
  LineIndex =
    Fin seven

  Lines : Set
  Lines =
    LineIndex -> Line R

  Incident :
    Lines ->
    LineIndex ->
    Point R ->
    Set
  Incident lines i p =
    y-coordinate p ==
    add reals
      (multiply reals
        (slope (lines i))
        (x-coordinate p))
      (intercept (lines i))

  DistinctLines :
    Lines ->
    Set
  DistinctLines lines =
    (i j : LineIndex) ->
    i != j ->
    lines i != lines j

  ExactlyTwo :
    Lines ->
    Point R ->
    Set
  ExactlyTwo lines p =
    Exists LineIndex
      (\ i ->
        Exists LineIndex
          (\ j ->
            i != j
            and
            Incident lines i p
            and
            Incident lines j p
            and
            ((k : LineIndex) ->
              Incident lines k p ->
              k == i or k == j)))

  ExactlyThree :
    Lines ->
    Point R ->
    Set
  ExactlyThree lines p =
    Exists LineIndex
      (\ i ->
        Exists LineIndex
          (\ j ->
            Exists LineIndex
              (\ k ->
                i != j
                and
                i != k
                and
                j != k
                and
                Incident lines i p
                and
                Incident lines j p
                and
                Incident lines k p
                and
                ((ell : LineIndex) ->
                  Incident lines ell p ->
                  ell == i or ell == j or ell == k))))

  AtLeastSixTriplePoints :
    Lines ->
    Set
  AtLeastSixTriplePoints lines =
    Exists (Fin six -> Point R)
      (\ points ->
        Injective points
        and
        ((i : Fin six) ->
          ExactlyThree lines (points i)))

  AtLeastFourDoublePoints :
    Lines ->
    Set
  AtLeastFourDoublePoints lines =
    Exists (Fin four -> Point R)
      (\ points ->
        Injective points
        and
        ((i : Fin four) ->
          ExactlyTwo lines (points i)))

  proposition : Set
  proposition =
    Not
      (Exists Lines
        (\ lines ->
          DistinctLines lines
          and
          AtLeastSixTriplePoints lines
          and
          AtLeastFourDoublePoints lines))

putnam-1973-a6 : Set1
putnam-1973-a6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1973A6Statement.proposition reals
