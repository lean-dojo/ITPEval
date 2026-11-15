-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_a1:
-- no four consecutive binomial coefficients with positive lower index and
-- valid upper index form an arithmetic progression. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1972A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_
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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

ArithmeticProgression : Nat -> Nat -> Nat -> Nat -> Set
ArithmeticProgression a b c d =
  (d + b == c + c)
  and
  (c + a == b + b)

putnam-1972-a1 : Set
putnam-1972-a1 =
  (n : Nat) ->
  Positive n ->
  Not
    (Exists Nat
      (\ r ->
        Positive r
        and
        ((r + three) <=N n
        and
        ArithmeticProgression
          (choose n r)
          (choose n (r + one))
          (choose n (r + two))
          (choose n (r + three)))))
