-- Statement-only formalization of thousand-theorems corpus artifact Q132469
-- (thousand-theorems__agda__Q132469), "Fermat's Last Theorem": for every
-- natural exponent at least three, no three nonzero naturals satisfy the
-- Fermat equation. This file contains no proof.

{-# OPTIONS --safe #-}

module Q132469_fermat_s_last_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=_
infixr 8 _^_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

one : Nat
one =
  suc zero

three : Nat
three =
  suc (suc (suc zero))

_^_ : Nat -> Nat -> Nat
base ^ zero =
  one
base ^ suc exponent =
  base * (base ^ exponent)

FermatLastTheorem : Set
FermatLastTheorem =
  (n : Nat) ->
  three <= n ->
  (a b c : Nat) ->
  a != zero ->
  b != zero ->
  c != zero ->
  (a ^ n + b ^ n) != (c ^ n)
