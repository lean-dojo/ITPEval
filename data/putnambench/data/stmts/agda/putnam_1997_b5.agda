-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_b5
-- (putnambench__agda__putnam_1997_b5): for every natural n at least 2,
-- the height-n and height-(n-1) towers of 2 are congruent modulo n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infix 4 _<=N_

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  oneN
naturalPower base (suc exponent) =
  base * naturalPower base exponent

tetration : Nat -> Nat -> Nat
tetration base zero =
  oneN
tetration base (suc height) =
  naturalPower base (tetration base height)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

putnam-1997-b5 : Set
putnam-1997-b5 =
  (n : Nat) ->
  twoN <=N n ->
  naturalMod (tetration twoN n) n
  ==
  naturalMod (tetration twoN (n - oneN)) n
