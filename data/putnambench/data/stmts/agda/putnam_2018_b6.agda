-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_b6
-- (putnambench__agda__putnam_2018_b6): the cardinality bound for length-2018
-- sequences with entries in {1,2,3,4,5,6,10} and sum 3860. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Putnam2018B6 where

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

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

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
        (\ n -> lessOrEqual x (fromNat n))
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

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals base zero =
  oneR reals
naturalPower reals base (suc exponent) =
  multiply reals
    (naturalPower reals base exponent)
    base

sumFinNat :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFinNat {zero} terms =
  zero
sumFinNat {suc n} terms =
  terms fzero + sumFinNat (\ index -> terms (fsuc index))

Sequence2018 : Set
Sequence2018 =
  Fin 2018 -> Nat

SequenceEqual :
  Sequence2018 ->
  Sequence2018 ->
  Set
SequenceEqual left-sequence right-sequence =
  (index : Fin 2018) ->
  left-sequence index == right-sequence index

ValidEntry : Nat -> Set
ValidEntry value =
  (value == 1)
  or
  (value == 2)
  or
  (value == 3)
  or
  (value == 4)
  or
  (value == 5)
  or
  (value == 6)
  or
  (value == 10)

ValidSequence : Sequence2018 -> Set
ValidSequence sequence =
  ((index : Fin 2018) ->
    ValidEntry (sequence index))
  and
  (sumFinNat sequence == 3860)

putnam-2018-b6-bound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
putnam-2018-b6-bound reals =
  multiply reals
    (naturalPower reals (fromNat reals 2) 3860)
    (naturalPower reals
      (divide reals
        (fromNat reals 2018)
        (fromNat reals 2048))
      2018)

putnam-2018-b6 :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  Set
putnam-2018-b6 reals =
  Exists Nat
    (\ cardinality ->
      HasExtensionalCardinality
        SequenceEqual
        ValidSequence
        cardinality
      and
      lessOrEqual reals
        (fromNat reals cardinality)
        (putnam-2018-b6-bound reals))
