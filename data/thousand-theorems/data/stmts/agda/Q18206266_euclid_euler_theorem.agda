-- Statement-only formalization of thousand-theorems corpus artifact Q18206266
-- (thousand-theorems__agda__Q18206266), "Euclid–Euler theorem": every even
-- perfect natural number is 2^k times the prime Mersenne number 2^(k+1)-1
-- for some natural k. This file contains no proof.

{-# OPTIONS --safe #-}

module Q18206266_euclid_euler_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=_ _divides_ _member_
infixr 5 _and_
infixr 3 _or_
infixr 8 _^_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : P value

record _and_ (A B : Set) : Set where
  constructor conjunction
  field
    first : A
    second : B

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward : A -> B
    backward : B -> A

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 <= n
    only-trivial-divisors :
      (d : Nat) ->
      d divides n ->
      (d == 1) or (d == n)

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

data _member_ {A : Set} (x : A) : List A -> Set where
  here : {xs : List A} -> x member (cons x xs)
  there :
    {y : A} ->
    {xs : List A} ->
    x member xs ->
    x member (cons y xs)

data Bottom : Set where

data NoDuplicates {A : Set} : List A -> Set where
  no-duplicates-nil : NoDuplicates nil
  no-duplicates-cons :
    {x : A} ->
    {xs : List A} ->
    (x member xs -> Bottom) ->
    NoDuplicates xs ->
    NoDuplicates (cons x xs)

sum : List Nat -> Nat
sum nil = zero
sum (cons x xs) = x + sum xs

record IsDivisorSum (n total : Nat) : Set where
  field
    divisors : List Nat
    exact-divisors :
      (d : Nat) ->
      Iff (d member divisors) (d divides n)
    no-duplicate-divisors : NoDuplicates divisors
    sum-equation : sum divisors == total

_^_ : Nat -> Nat -> Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

Even : Nat -> Set
Even n =
  Exists Nat (\ half -> n == half + half)

Perfect : Nat -> Set
Perfect n =
  (1 <= n) and IsDivisorSum n (2 * n)

mersenne : Nat -> Nat
mersenne exponent =
  (2 ^ exponent) - 1

euclid-euler-converse : Set
euclid-euler-converse =
  (n : Nat) ->
  Even n ->
  Perfect n ->
  Exists Nat
    (\ k ->
      Prime (mersenne (suc k)) and
      (n == (2 ^ k) * mersenne (suc k)))
