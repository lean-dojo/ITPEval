-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_b3
-- (putnambench__agda__putnam_2003_b3): the factorial identity expressing n!
-- as a product of least common multiples of initial natural-number intervals.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

one : Nat
one =
  suc zero

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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

gcdWithFuel : Nat -> Nat -> Nat -> Nat
gcdWithFuel zero a b =
  a
gcdWithFuel (suc fuel) a zero =
  a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat -> Nat -> Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

naturalLCM : Nat -> Nat -> Nat
naturalLCM a b =
  naturalDiv (a * b) (naturalGCD a b)

factorial : Nat -> Nat
factorial zero =
  one
factorial (suc n) =
  suc n * factorial n

lcmThrough : Nat -> Nat
lcmThrough zero =
  one
lcmThrough (suc n) =
  naturalLCM (lcmThrough n) (suc n)

quotientLcmProduct : Nat -> Nat -> Nat
quotientLcmProduct n zero =
  one
quotientLcmProduct n (suc i) =
  quotientLcmProduct n i *
  lcmThrough (naturalDiv n (suc i))

putnam-2003-b3 : Set
putnam-2003-b3 =
  (n : Nat) ->
  Positive n ->
  factorial n == quotientLcmProduct n n
