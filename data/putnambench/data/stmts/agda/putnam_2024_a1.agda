-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1
-- (putnambench__agda__putnam_2024_a1): the positive natural exponents for
-- which 2a^n + 3b^n = 4c^n has positive natural solutions are exactly n = 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _<N_
infixr 8 _^_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

_^_ : Nat -> Nat -> Nat
base ^ zero =
  suc zero
base ^ suc exponent =
  base * (base ^ exponent)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

Positive : Nat -> Set
Positive n =
  zero <N n

HasPositiveSolution : Nat -> Set
HasPositiveSolution n =
  Exists Nat
    (\ a ->
      Positive a
      and
      Exists Nat
        (\ b ->
          Positive b
          and
          Exists Nat
            (\ c ->
              Positive c
              and
              two * (a ^ n) + three * (b ^ n) ==
                four * (c ^ n))))

putnam-2024-a1 : Set
putnam-2024-a1 =
  (n : Nat) ->
  Iff
    (Positive n and HasPositiveSolution n)
    (n == one)
