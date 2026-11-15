-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_a3:
-- the integer part of the minimum of k + n/k over positive integers k equals
-- the integer part of the square root of 4n + 1. This file contains no proof.

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

intSuccessor : Int -> Int
intSuccessor (pos n) =
  pos (suc n)
intSuccessor (negsuc zero) =
  pos zero
intSuccessor (negsuc (suc n)) =
  negsuc n

embedInt :
  {R : Set} ->
  (Nat -> R) ->
  (R -> R) ->
  Int ->
  R
embedInt fromNatural negateR (pos n) =
  fromNatural n
embedInt fromNatural negateR (negsuc n) =
  negateR (fromNatural (suc n))

data PositiveInt : Int -> Set where
  positive : {n : Nat} -> PositiveInt (pos (suc n))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    floor : R -> Int

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

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

    floor-lower :
      (x : R) ->
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper :
      (x : R) ->
      lessOrEqual
        x
        (embedInt fromNat negate (intSuccessor (floor x)))
      and
      x != embedInt fromNat negate (intSuccessor (floor x))

open CompleteOrderedRealField

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals =
  embedInt (fromNat reals) (negate reals)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

MinimumValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R ->
  Set
MinimumValue {R} reals n minimum =
  ((k : Int) ->
    PositiveInt k ->
    lessOrEqual reals
      minimum
      (add reals
        (fromInt reals k)
        (divide reals
          (fromInt reals n)
          (fromInt reals k))))
  and
  Exists Int
    (\ k ->
      PositiveInt k
      and
      minimum ==
      add reals
        (fromInt reals k)
        (divide reals
          (fromInt reals n)
          (fromInt reals k)))

module Putnam1973A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  four : R
  four =
    fromNat reals (suc (suc (suc (suc zero))))

  radicand : Int -> R
  radicand n =
    add reals
      (multiply reals four (fromInt reals n))
      (oneR reals)

  proposition : Set
  proposition =
    (b : Int -> R) ->
    ((n : Int) -> MinimumValue reals n (b n)) ->
    (n : Int) ->
    PositiveInt n ->
    floor reals (b n) ==
    floor reals (squareRoot reals (radicand n))

putnam-1973-a3 : Set1
putnam-1973-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1973A3Statement.proposition reals
