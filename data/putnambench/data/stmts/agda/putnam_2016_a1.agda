-- Statement-only formalization of PutnamBench corpus artifact putnam_2016_a1
-- (putnambench__agda__putnam_2016_a1): the smallest positive derivative
-- order for which every integer polynomial has values divisible by 2016 at
-- every integer argument is 8. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2016A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 3 _and_

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

one : Nat
one =
  suc zero

eight : Nat
eight =
  8

Positive : Nat -> Set
Positive n =
  one <=N n

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

Polynomial : Set
Polynomial =
  List Int

evaluate : Polynomial -> Int -> Int
evaluate [] x =
  pos zero
evaluate (coefficient ∷ coefficients) x =
  addInt coefficient
    (multiplyInt x (evaluate coefficients x))

derivativeFrom : Nat -> Polynomial -> Polynomial
derivativeFrom multiplier [] =
  []
derivativeFrom multiplier (coefficient ∷ coefficients) =
  multiplyInt (pos multiplier) coefficient
  ∷ derivativeFrom (suc multiplier) coefficients

derivative : Polynomial -> Polynomial
derivative [] =
  []
derivative (constant ∷ coefficients) =
  derivativeFrom one coefficients

iterateDerivative : Nat -> Polynomial -> Polynomial
iterateDerivative zero polynomial =
  polynomial
iterateDerivative (suc order) polynomial =
  iterateDerivative order (derivative polynomial)

DividesInt : Int -> Int -> Set
DividesInt divisor dividend =
  Exists Int
    (\ quotient ->
      multiplyInt divisor quotient == dividend)

modulus : Int
modulus =
  pos 2016

GoodOrder : Nat -> Set
GoodOrder order =
  Positive order
  and
  ((polynomial : Polynomial) ->
    (argument : Int) ->
    DividesInt modulus
      (evaluate (iterateDerivative order polynomial) argument))

putnam-2016-a1 : Set
putnam-2016-a1 =
  GoodOrder eight
  and
  ((order : Nat) ->
    GoodOrder order ->
    eight <=N order)
