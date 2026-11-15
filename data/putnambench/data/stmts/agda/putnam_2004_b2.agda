-- Statement-only formalization of PutnamBench corpus artifact putnam_2004_b2
-- (putnambench__agda__putnam_2004_b2): the strict factorial-ratio inequality
-- for two positive integers. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2004B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

Positive : Nat -> Set
Positive n =
  suc zero <=N n

record RationalField (Q : Set) : Set1 where
  field
    zeroQ oneQ : Q
    add multiply : Q -> Q -> Q
    negate inverse : Q -> Q
    lessOrEqual : Q -> Q -> Set
    fromNat : Nat -> Q
    fromInt : Int -> Q

    one-not-zero :
      oneQ != zeroQ

    add-commutative :
      (x y : Q) -> add x y == add y x
    add-associative :
      (x y z : Q) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : Q) -> add x zeroQ == x
    add-inverse :
      (x : Q) -> add x (negate x) == zeroQ

    multiply-commutative :
      (x y : Q) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : Q) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : Q) -> multiply x oneQ == x
    multiply-zero :
      (x : Q) -> multiply x zeroQ == zeroQ
    distribute :
      (x y z : Q) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroQ == zeroQ
    multiply-inverse :
      (x : Q) ->
      x != zeroQ ->
      multiply x (inverse x) == oneQ

    order-reflexive :
      (x : Q) -> lessOrEqual x x
    order-transitive :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : Q) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : Q) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : Q) ->
      lessOrEqual zeroQ x ->
      lessOrEqual zeroQ y ->
      lessOrEqual zeroQ (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroQ oneQ and zeroQ != oneQ

    fromNat-zero :
      fromNat zero == zeroQ
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneQ
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

    fromInt-nonnegative :
      (n : Nat) ->
      fromInt (pos n) == fromNat n
    fromInt-negative :
      (n : Nat) ->
      fromInt (negsuc n) == negate (fromNat (suc n))

    every-element-is-ratio :
      (x : Q) ->
      Exists Int
        (\ numerator ->
          Exists Nat
            (\ denominator-minus-one ->
              x ==
              multiply
                (fromInt numerator)
                (inverse
                  (fromNat (suc denominator-minus-one)))))

open RationalField

divide :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Q
divide rationals x y =
  multiply rationals x (inverse rationals y)

StrictLess :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Set
StrictLess rationals x y =
  lessOrEqual rationals x y and x != y

naturalPower :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Nat ->
  Q
naturalPower rationals x zero =
  oneQ rationals
naturalPower rationals x (suc n) =
  multiply rationals
    (naturalPower rationals x n)
    x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

factorialRatio :
  {Q : Set} ->
  RationalField Q ->
  Nat ->
  Q
factorialRatio rationals n =
  divide rationals
    (fromNat rationals (factorial n))
    (naturalPower rationals (fromNat rationals n) n)

putnam-2004-b2 : Set1
putnam-2004-b2 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  StrictLess rationals
    (factorialRatio rationals (m + n))
    (multiply rationals
      (factorialRatio rationals m)
      (factorialRatio rationals n))
