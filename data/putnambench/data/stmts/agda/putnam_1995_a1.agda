-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_a1:
-- a multiplication-closed set of real numbers partitioned into two disjoint
-- triple-product-closed subsets has a multiplication-closed part. This file contains no proof.

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
  constructor iff
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

module Putnam1995A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Subset : Set1
  Subset =
    R -> Set

  SubsetOf :
    Subset ->
    Subset ->
    Set
  SubsetOf A B =
    (x : R) ->
    A x ->
    B x

  Union :
    Subset ->
    Subset ->
    Subset
  Union A B x =
    A x or B x

  SetEqual :
    Subset ->
    Subset ->
    Set
  SetEqual A B =
    (x : R) ->
    Iff (A x) (B x)

  Disjoint :
    Subset ->
    Subset ->
    Set
  Disjoint A B =
    (x : R) ->
    A x ->
    B x ->
    Bottom

  ClosedUnderMultiplication :
    Subset ->
    Set
  ClosedUnderMultiplication A =
    (a b : R) ->
    A a ->
    A b ->
    A (multiply reals a b)

  ClosedUnderTripleMultiplication :
    Subset ->
    Set
  ClosedUnderTripleMultiplication A =
    (a b c : R) ->
    A a ->
    A b ->
    A c ->
    A (multiply reals (multiply reals a b) c)

  proposition : Set1
  proposition =
    (S : Subset) ->
    ClosedUnderMultiplication S ->
    (T U : Subset) ->
    (SubsetOf T S and SubsetOf U S) ->
    SetEqual (Union T U) S ->
    Disjoint T U ->
    ClosedUnderTripleMultiplication T ->
    ClosedUnderTripleMultiplication U ->
    ClosedUnderMultiplication T
    or
    ClosedUnderMultiplication U

putnam-1995-a1 : Set1
putnam-1995-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1995A1Statement.proposition reals
