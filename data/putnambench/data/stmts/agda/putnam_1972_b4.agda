-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_b4:
-- for every natural n greater than one, an integer polynomial in three
-- variables recovers x from x^n, x^(n+1), and x+x^(n+2). This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data GreaterThanOne : Nat -> Set where
  greater-than-one :
    {k : Nat} ->
    GreaterThanOne (suc (suc k))

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

powerInt : Int -> Nat -> Int
powerInt x zero =
  pos (suc zero)
powerInt x (suc n) =
  multiplyInt x (powerInt x n)

record Monomial : Set where
  constructor monomial
  field
    coefficient    : Int
    firstExponent  : Nat
    secondExponent : Nat
    thirdExponent  : Nat

open Monomial

Polynomial : Set
Polynomial =
  List Monomial

evaluateMonomial : Monomial -> Int -> Int -> Int -> Int
evaluateMonomial term x y z =
  multiplyInt
    (coefficient term)
    (multiplyInt
      (powerInt x (firstExponent term))
      (multiplyInt
        (powerInt y (secondExponent term))
        (powerInt z (thirdExponent term))))

evaluatePolynomial : Polynomial -> Int -> Int -> Int -> Int
evaluatePolynomial [] x y z =
  pos zero
evaluatePolynomial (term ∷ terms) x y z =
  addInt
    (evaluateMonomial term x y z)
    (evaluatePolynomial terms x y z)

putnam-1972-b4 : Set
putnam-1972-b4 =
  (n : Nat) ->
  GreaterThanOne n ->
  Exists Polynomial
    (\ polynomial ->
      (x : Int) ->
      x ==
      evaluatePolynomial polynomial
        (powerInt x n)
        (powerInt x (suc n))
        (addInt x (powerInt x (suc (suc n)))))
