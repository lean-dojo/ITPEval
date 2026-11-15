-- Statement-only formalization of PutnamBench corpus artifact putnam_1998_a4:
-- the recursively concatenated decimal strings divisible by 11 occur exactly at
-- indices congruent to 1 modulo 6. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 2 _iff_
infixr 3 _and_
infixr 5 _++_
infix 4 _<=_ _divides_

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

record Exists (A : Set) (property : A -> Set) : Set where
  constructor witness
  field
    value : A
    holds : property value

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  constructor quotient
  field
    factor : Nat
    equation : divisor * factor == dividend

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

fromDigitsAcc : Nat -> List Nat -> Nat
fromDigitsAcc accumulator [] =
  accumulator
fromDigitsAcc accumulator (digit ∷ digits) =
  fromDigitsAcc (10 * accumulator + digit) digits

fromDigits : List Nat -> Nat
fromDigits digits =
  fromDigitsAcc zero digits

CongruentOneModSix : Nat -> Set
CongruentOneModSix n =
  Exists Nat (\ q -> n == 1 + 6 * q)

putnam-1998-a4 : Set
putnam-1998-a4 =
  (A : Nat -> List Nat) ->
  A 1 == 0 ∷ [] ->
  A 2 == 1 ∷ [] ->
  ((n : Nat) ->
    1 <= n ->
    A (n + 2) == A (n + 1) ++ A n) ->
  (n : Nat) ->
  ((1 <= n) and (11 divides fromDigits (A n)))
    iff CongruentOneModSix n
