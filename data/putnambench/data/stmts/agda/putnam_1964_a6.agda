-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a6:
-- repeated nonmaximal distances among a finite set of real points force the
-- distance ratio of any two distinct ordered pairs to be rational. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1964A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

fromInt :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Predicate : Set -> Set1
Predicate A =
  A -> Set

record Pair (A : Set) : Set where
  constructor pair
  field
    first-coordinate  : A
    second-coordinate : A

open Pair

record FiniteSubset
  {A : Set}
  (S : Predicate A) : Set where
  field
    size :
      Nat
    enumerate :
      Fin size -> A
    enumerated-member :
      (i : Fin size) -> S (enumerate i)
    enumeration-complete :
      (x : A) ->
      S x ->
      Exists (Fin size) (\ i -> x == enumerate i)

module Putnam1964A6Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  OrderedPair :
    Predicate R ->
    Pair R ->
    Set
  OrderedPair S p =
    S (first-coordinate p)
    and
    S (second-coordinate p)
    and
    StrictLess reals
      (first-coordinate p)
      (second-coordinate p)

  distance :
    Pair R ->
    R
  distance p =
    subtract reals
      (second-coordinate p)
      (first-coordinate p)

  IsRational :
    R ->
    Set
  IsRational x =
    Exists Int
      (\ numerator ->
        Exists Int
          (\ denominator ->
            denominator != pos zero
            and
            x ==
            divide reals
              (fromInt reals numerator)
              (fromInt reals denominator)))

  RepeatsEveryNonmaximalDistance :
    Predicate R ->
    Set
  RepeatsEveryNonmaximalDistance S =
    (p : Pair R) ->
    OrderedPair S p ->
    Exists (Pair R)
      (\ m ->
        OrderedPair S m
        and
        StrictLess reals (distance p) (distance m)) ->
    Exists (Pair R)
      (\ q ->
        OrderedPair S q
        and
        q != p
        and
        distance p == distance q)

  proposition : Set1
  proposition =
    (S : Predicate R) ->
    FiniteSubset S ->
    RepeatsEveryNonmaximalDistance S ->
    (p q : Pair R) ->
    OrderedPair S p ->
    OrderedPair S q ->
    q != p ->
    IsRational
      (divide reals (distance p) (distance q))

putnam-1964-a6 : Set1
putnam-1964-a6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964A6Statement.proposition reals
