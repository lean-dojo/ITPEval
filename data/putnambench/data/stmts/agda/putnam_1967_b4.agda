-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_b4:
-- after divisor-indexed toggling operations on finitely many lockers, exactly
-- the perfect-square-indexed lockers are open. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _<=_ _divides_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

record _divides_ (divisor dividend : Nat) : Set where
  constructor quotient
  field
    factor   : Nat
    equation : divisor * factor == dividend

one : Nat
one =
  suc zero

InRange : Nat -> Nat -> Set
InRange i n =
  (one <= i) and (i <= n)

notBool : Bool -> Bool
notBool false =
  true
notBool true =
  false

putnam-1967-b4 : Set
putnam-1967-b4 =
  (n : Nat) ->
  (lockers : Nat -> Nat -> Bool) ->
  one <= n ->
  ((i : Nat) ->
    InRange i n ->
    lockers zero i == false) ->
  ((k i : Nat) ->
    InRange k n ->
    InRange i n ->
    ((k divides i ->
      lockers k i == notBool (lockers (k - one) i))
    and
    (Not (k divides i) ->
      lockers k i == lockers (k - one) i))) ->
  (i : Nat) ->
  InRange i n ->
  Iff
    (lockers n i == true)
    (Exists Nat (\ j -> j * j == i))
