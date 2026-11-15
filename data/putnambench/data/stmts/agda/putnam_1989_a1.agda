-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_a1:
-- exactly one positive prime has an ordinary base-10 representation alternating
-- 1s and 0s, beginning and ending with 1. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _divides_
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

record _divides_ (divisor dividend : Nat) : Set where
  constructor divisibility
  field
    quotient          : Nat
    division-equation : dividend == divisor * quotient

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

hundred : Nat
hundred =
  100

record Prime (p : Nat) : Set where
  field
    at-least-two :
      two <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d divides p ->
      (d == one) or (d == p)

alternatingDecimal : Nat -> Nat
alternatingDecimal zero =
  one
alternatingDecimal (suc pairs) =
  hundred * alternatingDecimal pairs + one

AlternatingPrime : Nat -> Set
AlternatingPrime p =
  Prime p
  and
  Exists Nat
    (\ pairs -> p == alternatingDecimal pairs)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (item : A) ->
      P item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

putnam-1989-a1 : Set
putnam-1989-a1 =
  HasCardinality AlternatingPrime one
