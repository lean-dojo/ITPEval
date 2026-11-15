-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_a4
-- (putnambench__agda__putnam_2009_a4): whether every set of rational numbers
-- containing zero and closed under shifts by one and the stated reciprocal
-- operation contains all rationals; the requested answer is False. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {ell : Level} ->
  Set ell ->
  Set ell
Not A =
  A -> Bottom

_!=_ :
  {ell : Level} ->
  {A : Set ell} ->
  A ->
  A ->
  Set ell
x != y =
  Not (x == y)

record _and_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {element-level property-level : Level}
  (A : Set element-level)
  (P : A -> Set property-level) :
  Set (element-level ⊔ property-level) where

  constructor witness
  field
    value    : A
    property : P value

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
      (x y : Q) ->
      add x y == add y x
    add-associative :
      (x y z : Q) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : Q) ->
      add x zeroQ == x
    add-inverse :
      (x : Q) ->
      add x (negate x) == zeroQ

    multiply-commutative :
      (x y : Q) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : Q) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : Q) ->
      multiply x oneQ == x
    multiply-zero :
      (x : Q) ->
      multiply x zeroQ == zeroQ
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

module Putnam2009A4Statement
  {Q : Set}
  (rationals : RationalField Q) where

  ShiftClosed : (Q -> Set) -> Set
  ShiftClosed S =
    (x : Q) ->
    S x ->
    S (add rationals x (oneQ rationals))
    and
    S (subtract rationals x (oneQ rationals))

  ReciprocalClosed : (Q -> Set) -> Set
  ReciprocalClosed S =
    (x : Q) ->
    S x ->
    x != zeroQ rationals ->
    x != oneQ rationals ->
    S
      (divide rationals
        (oneQ rationals)
        (multiply rationals
          x
          (subtract rationals x (oneQ rationals))))

  ContainsAllRationals : (Q -> Set) -> Set
  ContainsAllRationals S =
    (r : Q) ->
    S r

  universal-claim : Set1
  universal-claim =
    (S : Q -> Set) ->
    S (zeroQ rationals) ->
    ShiftClosed S ->
    ReciprocalClosed S ->
    ContainsAllRationals S

putnam-2009-a4 : Set1
putnam-2009-a4 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  Iff
    (Putnam2009A4Statement.universal-claim rationals)
    Bottom
