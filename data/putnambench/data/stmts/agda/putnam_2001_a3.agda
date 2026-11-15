-- Statement-only formalization of PutnamBench corpus artifact putnam_2001_a3
-- (putnambench__agda__putnam_2001_a3): the integer parameters for which the
-- prescribed quartic factors into two nonconstant integer polynomials are
-- exactly the squares and twice the squares. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _iff_
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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negateInt : Int -> Int
negateInt (pos zero) =
  pos zero
negateInt (pos (suc n)) =
  negsuc n
negateInt (negsuc n) =
  pos (suc n)

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

zeroZ : Int
zeroZ =
  pos zero

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN + twoN

oneZ : Int
oneZ =
  pos oneN

twoZ : Int
twoZ =
  pos twoN

fourZ : Int
fourZ =
  pos fourN

Polynomial : Set
Polynomial =
  List Int

coefficient : Polynomial -> Nat -> Int
coefficient [] n =
  zeroZ
coefficient (c ∷ coefficients) zero =
  c
coefficient (c ∷ coefficients) (suc n) =
  coefficient coefficients n

PolynomialEqual : Polynomial -> Polynomial -> Set
PolynomialEqual p q =
  (n : Nat) ->
  coefficient p n == coefficient q n

addPolynomials : Polynomial -> Polynomial -> Polynomial
addPolynomials [] ys =
  ys
addPolynomials xs [] =
  xs
addPolynomials (x ∷ xs) (y ∷ ys) =
  addInt x y ∷ addPolynomials xs ys

scalePolynomial : Int -> Polynomial -> Polynomial
scalePolynomial scalar [] =
  []
scalePolynomial scalar (coefficient ∷ coefficients) =
  multiplyInt scalar coefficient ∷
  scalePolynomial scalar coefficients

multiplyPolynomials : Polynomial -> Polynomial -> Polynomial
multiplyPolynomials [] ys =
  []
multiplyPolynomials (x ∷ xs) [] =
  []
multiplyPolynomials (x ∷ xs) (y ∷ ys) =
  addPolynomials
    (scalePolynomial x (y ∷ ys))
    (zeroZ ∷ multiplyPolynomials xs (y ∷ ys))

Nonconstant : Polynomial -> Set
Nonconstant polynomial =
  Exists Nat
    (\ degree ->
      Positive degree
      and
      coefficient polynomial degree != zeroZ)

putnamPolynomial : Int -> Polynomial
putnamPolynomial m =
  squareInt (subtractInt m twoZ)
  ∷ zeroZ
  ∷ negateInt (addInt (multiplyInt twoZ m) fourZ)
  ∷ zeroZ
  ∷ oneZ
  ∷ []

Factorable : Int -> Set
Factorable m =
  Exists Polynomial
    (\ a ->
      Exists Polynomial
        (\ b ->
          PolynomialEqual
            (putnamPolynomial m)
            (multiplyPolynomials a b)
          and
          Nonconstant a
          and
          Nonconstant b))

Solution : Int -> Set
Solution m =
  Exists Int
    (\ k ->
      m == squareInt k
      or
      m == multiplyInt twoZ (squareInt k))

putnam-2001-a3 : Set
putnam-2001-a3 =
  (m : Int) ->
  Factorable m iff Solution m
