-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_b4
-- (putnambench__agda__putnam_2001_b4): emptiness of the intersection of all
-- positive iterated images of x -> x - 1/x on rationals other than -1, 0,
-- and 1. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2001B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _iff_

data Bottom : Set where

record Top : Set where
  constructor truth

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

record RationalField (Q : Set) : Set1 where
  field
    zeroQ oneQ : Q
    add multiply : Q -> Q -> Q
    negate inverse : Q -> Q
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

    fromNat-zero :
      fromNat zero == zeroQ
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneQ
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    fromInt-positive :
      (n : Nat) ->
      fromInt (pos n) == fromNat n
    fromInt-negative :
      (n : Nat) ->
      fromInt (negsuc n) == negate (fromNat (suc n))

    fraction-surjective :
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

subtract :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Q
subtract rationals x y =
  add rationals x (negate rationals y)

divide :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Q
divide rationals x y =
  multiply rationals x (inverse rationals y)

negativeOne :
  {Q : Set} ->
  RationalField Q ->
  Q
negativeOne rationals =
  negate rationals (oneQ rationals)

InS :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Set
InS rationals x =
  (x != negativeOne rationals)
  and
  ((x != zeroQ rationals)
  and
  (x != oneQ rationals))

record SElement {Q : Set} (rationals : RationalField Q) : Set where
  constructor element
  field
    rationalValue : Q
    belongsToS    : InS rationals rationalValue

open SElement

SameElement :
  {Q : Set} ->
  {rationals : RationalField Q} ->
  SElement rationals ->
  SElement rationals ->
  Set
SameElement x y =
  rationalValue x == rationalValue y

iterate :
  {A : Set} ->
  (A -> A) ->
  Nat ->
  A ->
  A
iterate f zero x =
  x
iterate f (suc n) x =
  f (iterate f n x)

putnamMap :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q
putnamMap rationals x =
  subtract rationals x
    (divide rationals (oneQ rationals) x)

HasPutnamFormula :
  {Q : Set} ->
  (rationals : RationalField Q) ->
  (SElement rationals -> SElement rationals) ->
  Set
HasPutnamFormula rationals f =
  (x : SElement rationals) ->
  rationalValue (f x) ==
  putnamMap rationals (rationalValue x)

InIteratedImage :
  {Q : Set} ->
  {rationals : RationalField Q} ->
  (SElement rationals -> SElement rationals) ->
  Nat ->
  SElement rationals ->
  Set
InIteratedImage {rationals = rationals} f n y =
  Exists (SElement rationals)
    (\ x -> SameElement (iterate f n x) y)

EmptyPositiveIteratedIntersection :
  {Q : Set} ->
  {rationals : RationalField Q} ->
  (SElement rationals -> SElement rationals) ->
  Set
EmptyPositiveIteratedIntersection
  {rationals = rationals} f =
  Not
    (Exists (SElement rationals)
      (\ y ->
        (n : Nat) ->
        Positive n ->
        InIteratedImage f n y))

putnam-2001-b4 : Set1
putnam-2001-b4 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  (f : SElement rationals -> SElement rationals) ->
  HasPutnamFormula rationals f ->
  EmptyPositiveIteratedIntersection f iff Top
