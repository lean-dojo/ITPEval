-- Statement-only formalization of PutnamBench corpus artifact putnam_2008_b4
-- (putnambench__agda__putnam_2008_b4): an integer polynomial that is
-- injective modulo p^2 on the first p^2 natural inputs is injective modulo
-- p^3 on the first p^3 natural inputs, for prime p. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _divides_
infixr 2 _or_

data _<_ : Nat -> Nat -> Set where
  zero<successor :
    {n : Nat} ->
    zero < suc n
  successor<successor :
    {m n : Nat} ->
    m < n ->
    suc m < suc n

record _divides_ (divisor dividend : Nat) : Set where
  constructor division
  field
    quotient : Nat
    division-equation :
      dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

record Prime (p : Nat) : Set where
  constructor prime
  field
    at-least-two :
      one < p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

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
  addInt
    coefficient
    (multiplyInt x (evaluate coefficients x))

record IntModEq
  (modulus : Nat)
  (left-value right-value : Int) : Set where
  constructor congruence
  field
    multiple : Int
    congruence-equation :
      left-value ==
      addInt right-value (multiplyInt (pos modulus) multiple)

InjectiveModuloOnInitialSegment :
  Nat ->
  Nat ->
  Polynomial ->
  Set
InjectiveModuloOnInitialSegment modulus bound polynomial =
  (i j : Nat) ->
  i < bound ->
  j < bound ->
  IntModEq modulus
    (evaluate polynomial (pos i))
    (evaluate polynomial (pos j)) ->
  i == j

putnam-2008-b4 : Set
putnam-2008-b4 =
  (p : Nat) ->
  Prime p ->
  (h : Polynomial) ->
  InjectiveModuloOnInitialSegment
    (power p two)
    (power p two)
    h ->
  InjectiveModuloOnInitialSegment
    (power p three)
    (power p three)
    h
