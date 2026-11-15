-- Statement-only formalization of PutnamBench corpus artifact putnam_1993_a6:
-- a self-describing infinite sequence of 2s and 3s is characterized by the
-- floor values of multiples of a real number. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
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

open CompleteOrderedRealField

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

successorInt : Int -> Int
successorInt (pos n) =
  pos (suc n)
successorInt (negsuc zero) =
  pos zero
successorInt (negsuc (suc n)) =
  negsuc n

record StandardFloor
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    floor : R -> Int

    floor-lower :
      (x : R) ->
      lessOrEqual reals
        (fromInt reals (floor x))
        x
    floor-upper :
      (x : R) ->
      StrictLess reals
        x
        (fromInt reals (successorInt (floor x)))
    floor-unique :
      (x : R) ->
      (z : Int) ->
      lessOrEqual reals (fromInt reals z) x ->
      StrictLess reals x (fromInt reals (successorInt z)) ->
      floor x == z

open StandardFloor

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

sumFirst : Nat -> (Nat -> Nat) -> Nat
sumFirst zero term =
  zero
sumFirst (suc n) term =
  sumFirst n term + term n

module Putnam1993A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (flooring : StandardFloor reals) where

  proposition : Set
  proposition =
    (seq : Nat -> Nat) ->
    ((n : Nat) ->
      (seq n == twoN) or (seq n == threeN)) ->
    ((n : Nat) ->
      Iff
        (seq n == twoN)
      (Exists Nat
        (\ N ->
          n ==
          sumFirst N
            (\ i -> seq i + oneN)))) ->
    Exists R
      (\ r ->
        (n : Nat) ->
        Iff
          (seq n == twoN)
        (Exists Nat
          (\ m ->
            pos (suc n) ==
            successorInt
              (floor flooring
                (multiply reals r (fromNat reals m))))))

putnam-1993-a6 : Set1
putnam-1993-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (flooring : StandardFloor reals) ->
  Putnam1993A6Statement.proposition reals flooring
