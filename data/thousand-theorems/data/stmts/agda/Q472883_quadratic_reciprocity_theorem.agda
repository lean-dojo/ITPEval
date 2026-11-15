-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q472883, "Quadratic reciprocity theorem": the
-- Legendre symbols of distinct odd primes and Jacobi symbols of odd natural
-- numbers obey the standard quadratic-reciprocity sign law. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q472883_quadratic_reciprocity_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _<=_ _!=_ _divides_
infixl 7 _*Z_
infixr 2 _or_

data Bottom : Set where

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  x == y -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record Prime (p : Nat) : Set where
  field
    at-least-two : two <= p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

record Odd (n : Nat) : Set where
  field
    half : Nat
    odd-equation : n == two * half + one

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

boolOr : Bool -> Bool -> Bool
boolOr true other =
  true
boolOr false other =
  other

squareCongruent : Nat -> Nat -> Nat -> Bool
squareCongruent modulus value root =
  natEqual
    (naturalMod (root * root) modulus)
    (naturalMod value modulus)

hasSquareResidueThrough : Nat -> Nat -> Nat -> Bool
hasSquareResidueThrough modulus value zero =
  squareCongruent modulus value zero
hasSquareResidueThrough modulus value (suc bound) =
  boolOr
    (squareCongruent modulus value (suc bound))
    (hasSquareResidueThrough modulus value bound)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

oneZ : Int
oneZ =
  pos one

minusOneZ : Int
minusOneZ =
  negsuc zero

intPower : Int -> Nat -> Int
intPower base zero =
  oneZ
intPower base (suc exponent) =
  base *Z intPower base exponent

legendreSymbol : Nat -> Nat -> Int
legendreSymbol modulus value
  with natEqual (naturalMod value modulus) zero
... | true =
  pos zero
... | false
  with hasSquareResidueThrough modulus value modulus
...   | true =
  oneZ
...   | false =
  minusOneZ

smallestDivisorFrom : Nat -> Nat -> Nat -> Nat
smallestDivisorFrom value candidate zero =
  value
smallestDivisorFrom value candidate (suc fuel)
  with natEqual (naturalMod value candidate) zero
... | true =
  candidate
... | false =
  smallestDivisorFrom value (suc candidate) fuel

smallestDivisor : Nat -> Nat
smallestDivisor value =
  smallestDivisorFrom value two value

jacobiFactorProduct : Nat -> Nat -> Nat -> Int
jacobiFactorProduct numerator denominator zero =
  oneZ
jacobiFactorProduct numerator denominator (suc fuel)
  with natEqual denominator zero
... | true =
  oneZ
... | false
  with natEqual denominator one
...   | true =
  oneZ
...   | false =
  legendreSymbol (smallestDivisor denominator) numerator *Z
    jacobiFactorProduct numerator
      (naturalDiv denominator (smallestDivisor denominator))
      fuel

jacobiSymbol : Nat -> Nat -> Int
jacobiSymbol numerator denominator =
  jacobiFactorProduct numerator denominator denominator

quadratic-reciprocity-theorem : Set
quadratic-reciprocity-theorem =
  (p q : Nat) ->
  Prime p ->
  Prime q ->
  p != two ->
  q != two ->
  p != q ->
  legendreSymbol q p *Z legendreSymbol p q
    ==
  intPower minusOneZ
    (naturalDiv p two * naturalDiv q two)

jacobi-quadratic-reciprocity-theorem : Set
jacobi-quadratic-reciprocity-theorem =
  (a b : Nat) ->
  Odd a ->
  Odd b ->
  jacobiSymbol a b
    ==
  intPower minusOneZ
    (naturalDiv a two * naturalDiv b two)
    *Z jacobiSymbol b a
