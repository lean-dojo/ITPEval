-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_b4
-- (putnambench__agda__putnam_2021_b4): for every Fibonacci index m greater
-- than 2, the remainder modulo F_m of the product of k^k for 1 <= k < F_m
-- is a Fibonacci number. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

weightedProduct : Nat -> Nat
weightedProduct zero =
  one
weightedProduct (suc upper) =
  weightedProduct upper *
  power (suc upper) (suc upper)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

putnam-2021-b4 : Set
putnam-2021-b4 =
  (F : Nat -> Nat) ->
  ((n : Nat) ->
    F (suc (suc n)) ==
    F (suc n) + F n) ->
  (F zero == zero and F one == one) ->
  (m : Nat) ->
  two <N m ->
  Exists Nat
    (\ p ->
      naturalMod
        (weightedProduct (F m - one))
        (F m)
      ==
      F p)
