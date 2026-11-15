-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_a5
-- (putnambench__agda__putnam_2002_a5): the Stern recurrence enumerates every
-- positive rational as a quotient of consecutive terms. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2002A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

SternRecurrence :
  {Q : Set} ->
  RationalField Q ->
  (Nat -> Q) ->
  Set
SternRecurrence rationals a =
  a zero == oneQ rationals
  and
  ((n : Nat) ->
    a (suc (n + n)) == a n
    and
    a (suc (suc (n + n))) ==
      add rationals (a n) (a (suc n)))

OccursAsConsecutiveQuotient :
  {Q : Set} ->
  RationalField Q ->
  (Nat -> Q) ->
  Q ->
  Set
OccursAsConsecutiveQuotient rationals a q =
  Exists Nat
    (\ n ->
      suc zero <=N n
      and
      divide rationals (a (n - suc zero)) (a n) == q)

putnam-2002-a5 : Set1
putnam-2002-a5 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  (a : Nat -> Q) ->
  SternRecurrence rationals a ->
  (q : Q) ->
  StrictLess rationals (zeroQ rationals) q ->
  OccursAsConsecutiveQuotient rationals a q
