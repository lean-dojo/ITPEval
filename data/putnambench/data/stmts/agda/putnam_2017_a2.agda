-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_a2:
-- a rational-function sequence defined from 1 and X by a nonlinear recurrence
-- has an integer-coefficient polynomial at every positive index.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2017A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

record Field (A : Set) : Set1 where
  field
    zeroA oneA : A
    add multiply : A -> A -> A
    negate inverse : A -> A

    one-not-zero :
      oneA != zeroA

    add-commutative :
      (x y : A) ->
      add x y == add y x
    add-associative :
      (x y z : A) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : A) ->
      add x zeroA == x
    add-inverse :
      (x : A) ->
      add x (negate x) == zeroA

    multiply-commutative :
      (x y : A) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : A) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : A) ->
      multiply x oneA == x
    multiply-zero :
      (x : A) ->
      multiply x zeroA == zeroA
    distribute :
      (x y z : A) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)

    inverse-zero :
      inverse zeroA == zeroA
    multiply-inverse :
      (x : A) ->
      x != zeroA ->
      multiply x (inverse x) == oneA

open Field

subtract :
  {A : Set} ->
  Field A ->
  A ->
  A ->
  A
subtract fieldA x y =
  add fieldA x (negate fieldA y)

divide :
  {A : Set} ->
  Field A ->
  A ->
  A ->
  A
divide fieldA x y =
  multiply fieldA x (inverse fieldA y)

square :
  {A : Set} ->
  Field A ->
  A ->
  A
square fieldA x =
  multiply fieldA x x

integerValue :
  {A : Set} ->
  Field A ->
  (Nat -> A) ->
  Int ->
  A
integerValue fieldA fromNat (pos n) =
  fromNat n
integerValue fieldA fromNat (negsuc n) =
  negate fieldA (fromNat (suc n))

record RationalField (A : Set) : Set1 where
  field
    fieldStructure : Field A
    fromNat : Nat -> A

    fromNat-zero :
      fromNat zero == zeroA fieldStructure
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) ==
      add fieldStructure (fromNat n) (oneA fieldStructure)
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) ==
      add fieldStructure (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) ==
      multiply fieldStructure (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    rational-generation :
      (x : A) ->
      Exists Int
        (\ numerator ->
          Exists Nat
            (\ denominator ->
              Positive denominator
              and
              (x ==
                divide fieldStructure
                  (integerValue fieldStructure fromNat numerator)
                  (fromNat denominator))))

open RationalField

Polynomial : Set -> Set
Polynomial A =
  List A

IntegerPolynomial : Set
IntegerPolynomial =
  List Int

coefficientAt :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Nat ->
  A
coefficientAt fieldA [] n =
  zeroA fieldA
coefficientAt fieldA (coefficient ∷ coefficients) zero =
  coefficient
coefficientAt fieldA (coefficient ∷ coefficients) (suc n) =
  coefficientAt fieldA coefficients n

PolynomialEqual :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Polynomial A ->
  Set
PolynomialEqual fieldA p q =
  (n : Nat) ->
  coefficientAt fieldA p n ==
  coefficientAt fieldA q n

zeroPolynomial :
  {A : Set} ->
  Polynomial A
zeroPolynomial =
  []

onePolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A
onePolynomial fieldA =
  oneA fieldA ∷ []

variablePolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A
variablePolynomial fieldA =
  zeroA fieldA ∷ oneA fieldA ∷ []

addPolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Polynomial A ->
  Polynomial A
addPolynomial fieldA [] q =
  q
addPolynomial fieldA p [] =
  p
addPolynomial fieldA (a ∷ p) (b ∷ q) =
  add fieldA a b ∷ addPolynomial fieldA p q

negatePolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Polynomial A
negatePolynomial fieldA [] =
  []
negatePolynomial fieldA (a ∷ p) =
  negate fieldA a ∷ negatePolynomial fieldA p

scalePolynomial :
  {A : Set} ->
  Field A ->
  A ->
  Polynomial A ->
  Polynomial A
scalePolynomial fieldA scalar [] =
  []
scalePolynomial fieldA scalar (a ∷ p) =
  multiply fieldA scalar a ∷ scalePolynomial fieldA scalar p

multiplyPolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Polynomial A ->
  Polynomial A
multiplyPolynomial fieldA [] q =
  []
multiplyPolynomial fieldA (a ∷ p) q =
  addPolynomial fieldA
    (scalePolynomial fieldA a q)
    (zeroA fieldA ∷ multiplyPolynomial fieldA p q)

mapIntegerPolynomial :
  {A : Set} ->
  Field A ->
  (Nat -> A) ->
  IntegerPolynomial ->
  Polynomial A
mapIntegerPolynomial fieldA fromNat [] =
  []
mapIntegerPolynomial fieldA fromNat (coefficient ∷ coefficients) =
  integerValue fieldA fromNat coefficient
  ∷
  mapIntegerPolynomial fieldA fromNat coefficients

NonzeroPolynomial :
  {A : Set} ->
  Field A ->
  Polynomial A ->
  Set
NonzeroPolynomial fieldA p =
  Not (PolynomialEqual fieldA p zeroPolynomial)

record RationalFunctionField
  {A : Set}
  (rationals : RationalField A)
  (K : Set) :
  Set1 where

  private
    rationalField : Field A
    rationalField =
      fieldStructure rationals

  field
    functionField : Field K
    polynomialEmbedding : Polynomial A -> K

    embedding-zero :
      polynomialEmbedding zeroPolynomial ==
      zeroA functionField
    embedding-one :
      polynomialEmbedding (onePolynomial rationalField) ==
      oneA functionField
    embedding-addition :
      (p q : Polynomial A) ->
      polynomialEmbedding (addPolynomial rationalField p q) ==
      add functionField
        (polynomialEmbedding p)
        (polynomialEmbedding q)
    embedding-negation :
      (p : Polynomial A) ->
      polynomialEmbedding (negatePolynomial rationalField p) ==
      negate functionField (polynomialEmbedding p)
    embedding-multiplication :
      (p q : Polynomial A) ->
      polynomialEmbedding (multiplyPolynomial rationalField p q) ==
      multiply functionField
        (polynomialEmbedding p)
        (polynomialEmbedding q)

    embedding-respects-equality :
      (p q : Polynomial A) ->
      PolynomialEqual rationalField p q ->
      polynomialEmbedding p == polynomialEmbedding q
    embedding-reflects-equality :
      (p q : Polynomial A) ->
      polynomialEmbedding p == polynomialEmbedding q ->
      PolynomialEqual rationalField p q

    fraction-representation :
      (r : K) ->
      Exists (Polynomial A)
        (\ numerator ->
          Exists (Polynomial A)
            (\ denominator ->
              NonzeroPolynomial rationalField denominator
              and
              (r ==
                divide functionField
                  (polynomialEmbedding numerator)
                  (polynomialEmbedding denominator))))

open RationalFunctionField

integerPolynomialImage :
  {A K : Set} ->
  (rationals : RationalField A) ->
  RationalFunctionField rationals K ->
  IntegerPolynomial ->
  K
integerPolynomialImage rationals rationalFunctions p =
  polynomialEmbedding rationalFunctions
    (mapIntegerPolynomial
      (fieldStructure rationals)
      (fromNat rationals)
      p)

module Putnam2017A2Statement
  {A K : Set}
  (rationals : RationalField A)
  (rationalFunctions : RationalFunctionField rationals K) where

  rationalField : Field A
  rationalField =
    fieldStructure rationals

  functionFieldStructure : Field K
  functionFieldStructure =
    functionField rationalFunctions

  X : K
  X =
    polynomialEmbedding rationalFunctions
      (variablePolynomial rationalField)

  Recurrence : (Nat -> K) -> Set
  Recurrence Q =
    (k : Nat) ->
    Q (suc (suc k))
    ==
    divide functionFieldStructure
      (subtract functionFieldStructure
        (square functionFieldStructure (Q (suc k)))
        (oneA functionFieldStructure))
      (Q k)

  HasIntegerPolynomialCoefficients : K -> Set
  HasIntegerPolynomialCoefficients value =
    Exists IntegerPolynomial
      (\ p ->
        value ==
        integerPolynomialImage rationals rationalFunctions p)

  proposition : Set
  proposition =
    (Q : Nat -> K) ->
    Q zero == oneA functionFieldStructure ->
    Q (suc zero) == X ->
    Recurrence Q ->
    (n : Nat) ->
    Positive n ->
    HasIntegerPolynomialCoefficients (Q n)

putnam-2017-a2 : Set1
putnam-2017-a2 =
  (A : Set) ->
  (rationals : RationalField A) ->
  (K : Set) ->
  (rationalFunctions : RationalFunctionField rationals K) ->
  Putnam2017A2Statement.proposition rationals rationalFunctions
