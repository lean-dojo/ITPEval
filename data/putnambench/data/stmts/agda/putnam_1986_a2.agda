-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_a2:
-- the units digit of floor(10^20000 / (10^100 + 3)) is 3. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Putnam1986A2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

one : Nat
one =
  suc zero

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  power base exponent * base

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

putnam-1986-a2 : Set
putnam-1986-a2 =
  naturalMod
    (naturalDiv
      (power 10 20000)
      (power 10 100 + 3))
    10
  ≡ 3
