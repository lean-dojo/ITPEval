-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a2
-- (putnambench__agda__putnam_2015_a2): the odd prime factor 181 of the
-- 2015th term of the integer recurrence a_n = 4 a_(n-1) - a_(n-2).
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _dividesN_ _dividesZ_
infixl 6 _+Z_ _-Z_
infixl 7 _*Z_
infixr 3 _and_
infixr 2 _or_

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

record _dividesN_ (divisor dividend : Nat) : Set where
  constructor natural-divisibility
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record Prime (n : Nat) : Set where
  field
    at-least-two :
      2 <=N n
    only-trivial-divisors :
      (d : Nat) ->
      d dividesN n ->
      (d == 1) or (d == n)

Odd : Nat -> Set
Odd n =
  Exists Nat (\ k -> n == 2 * k + 1)

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

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

negateZ : Int -> Int
negateZ (pos n) =
  negative n
negateZ (negsuc n) =
  pos (suc n)

_-Z_ : Int -> Int -> Int
x -Z y =
  x +Z negateZ y

record _dividesZ_ (divisor dividend : Int) : Set where
  constructor integer-divisibility
  field
    quotient : Int
    equation : divisor *Z quotient == dividend

putnam-2015-a2-solution : Nat
putnam-2015-a2-solution =
  181

InitialValues : (Nat -> Int) -> Set
InitialValues a =
  (a 0 == pos 1)
  and
  (a 1 == pos 2)

Recurrence : (Nat -> Int) -> Set
Recurrence a =
  (n : Nat) ->
  2 <=N n ->
  a n == (pos 4 *Z a (n - 1)) -Z a (n - 2)

putnam-2015-a2 : Set
putnam-2015-a2 =
  (a : Nat -> Int) ->
  InitialValues a ->
  Recurrence a ->
  Odd putnam-2015-a2-solution
  and
  Prime putnam-2015-a2-solution
  and
  (pos putnam-2015-a2-solution dividesZ a 2015)
