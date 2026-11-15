-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q632546, "Bertrand's postulate": every nonzero
-- natural number n has a prime p with n < p and p <= 2 * n. This file contains no proof.

{-# OPTIONS --safe #-}

module Q632546BertrandsPostulate where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<=_ _<_ _divides_
infixr 5 _and_
infixr 3 _or_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

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

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

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

bertrands-postulate : Set
bertrands-postulate =
  (n : Nat) ->
  n != zero ->
  Exists Nat
    (\ p ->
      Prime p and
      ((n < p) and (p <= two * n)))
