-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_a2:
-- for every nonnegative integer k, the finite sum from j = 0 through k of
-- 2^(k - j) times the binomial coefficient (k + j choose j) equals 4^k.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2020A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

one : Nat
one =
  suc zero

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc j) =
  zero
choose (suc n) (suc j) =
  choose n (suc j) + choose n j

sumThrough : Nat -> (Nat -> Nat) -> Nat
sumThrough zero term =
  term zero
sumThrough (suc k) term =
  sumThrough k term + term (suc k)

putnam-2020-a2 : Set
putnam-2020-a2 =
  (k : Nat) ->
  sumThrough k
    (\ j ->
      power 2 (k - j) * choose (k + j) j)
  ==
  power 4 k
