-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_b2
-- (putnambench__agda__putnam_2023_b2): the minimum number of ones in the
-- binary representation of a positive multiple of 2023 is three. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infix 4 _<=N_
infixr 3 _and_

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

one two three : Nat
one =
  suc zero
two =
  suc one
three =
  suc two

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

binaryOneCountWithFuel : Nat -> Nat -> Nat
binaryOneCountWithFuel zero n =
  zero
binaryOneCountWithFuel (suc fuel) zero =
  zero
binaryOneCountWithFuel (suc fuel) (suc n) =
  naturalMod (suc n) two +
  binaryOneCountWithFuel fuel (naturalDiv (suc n) two)

binaryOneCount : Nat -> Nat
binaryOneCount n =
  binaryOneCountWithFuel n n

putnam-2023-b2 : Set
putnam-2023-b2 =
  ((n : Nat) ->
    Positive n ->
    three <=N binaryOneCount (2023 * n))
  and
  Exists Nat
    (\ n ->
      Positive n
      and
      binaryOneCount (2023 * n) == three)
