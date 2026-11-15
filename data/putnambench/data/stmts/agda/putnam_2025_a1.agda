-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1:
-- two positive coprime natural-number sequences related by a rational
-- recurrence have only finitely many indices where the transformed terms are
-- not coprime. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _∣_ _~Q_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) ->
      d ∣ a ->
      d ∣ b ->
      d ∣ g

Coprime : Nat -> Nat -> Set
Coprime a b =
  IsGCD a b one

record NonnegativeFraction : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

open NonnegativeFraction

_~Q_ : NonnegativeFraction -> NonnegativeFraction -> Set
x ~Q y =
  numerator x * denominator y ==
  numerator y * denominator x

data Member {A : Set} (x : A) : List A -> Set where
  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)
  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

record FiniteSubset (P : Nat -> Set) : Set where
  field
    elements : List Nat
    complete :
      (k : Nat) ->
      P k ->
      Member k elements

sequenceRatio :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Nat ->
  NonnegativeFraction
sequenceRatio m n k =
  fraction (m k) (n k)

transformedRatio :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Nat ->
  NonnegativeFraction
transformedRatio m n k =
  fraction
    (two * m k + one)
    (two * n k + one)

ExceptionalIndex :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Nat ->
  Set
ExceptionalIndex m n k =
  Not
    (Coprime
      (two * m k + one)
      (two * n k + one))

putnam-2025-a1 : Set
putnam-2025-a1 =
  (m n : Nat -> Nat) ->
  ((k : Nat) -> Positive (m k)) ->
  ((k : Nat) -> Positive (n k)) ->
  m zero != n zero ->
  ((k : Nat) ->
    Positive k ->
    Coprime (m k) (n k)) ->
  ((k : Nat) ->
    sequenceRatio m n (suc k) ~Q
    transformedRatio m n k) ->
  FiniteSubset (ExceptionalIndex m n)
