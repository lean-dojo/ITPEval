-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_b3
-- (putnambench__agda__putnam_2018_b3): the positive integers below 10^100
-- satisfying three divisibility conditions, characterized by four powers of 2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _<=N_ _<N_ _divides_
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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

_divides_ : Nat -> Nat -> Set
divisor divides dividend =
  Exists Nat
    (\ quotient ->
      divisor * quotient == dividend)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  power base exponent * base

Positive : Nat -> Set
Positive n =
  one <=N n

Qualifies : Nat -> Set
Qualifies n =
  Positive n
  and
  n <N power 10 100
  and
  n divides power two n
  and
  (n - one) divides (power two n - one)
  and
  (n - two) divides (power two n - two)

Solution : Nat -> Set
Solution n =
  n == power two 2
  or
  n == power two 4
  or
  n == power two 16
  or
  n == power two 256

putnam-2018-b3 : Set
putnam-2018-b3 =
  (n : Nat) ->
  Iff (Qualifies n) (Solution n)
