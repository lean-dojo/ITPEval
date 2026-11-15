-- Statement-only formalization of Thousand Theorems corpus artifact Q193910
-- (thousand-theorems__agda__Q193910), "Euler's theorem": if two natural
-- numbers are coprime, raising the first to the totient of the second is
-- congruent to one modulo the second. This file contains no proof.

{-# OPTIONS --safe #-}

module Q193910_euler_s_theorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

one : Nat
one =
  suc zero

_^_ : Nat -> Nat -> Nat
base ^ zero =
  one
base ^ suc exponent =
  base * (base ^ exponent)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
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

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc b) =
  false
natEqual (suc a) zero =
  false
natEqual (suc a) (suc b) =
  natEqual a b

Coprime : Nat -> Nat -> Set
Coprime a b =
  naturalGCD a b == one

coprimeBool : Nat -> Nat -> Bool
coprimeBool a b =
  natEqual (naturalGCD a b) one

indicator : Bool -> Nat
indicator false =
  zero
indicator true =
  one

countCoprimeThrough : Nat -> Nat -> Nat
countCoprimeThrough n zero =
  zero
countCoprimeThrough n (suc bound) =
  countCoprimeThrough n bound +
  indicator (coprimeBool (suc bound) n)

totient : Nat -> Nat
totient n =
  countCoprimeThrough n n

ModEq : Nat -> Nat -> Nat -> Set
ModEq modulus lhs rhs =
  naturalMod lhs modulus == naturalMod rhs modulus

euler-s-theorem : Set
euler-s-theorem =
  (x n : Nat) ->
  Coprime x n ->
  ModEq n (x ^ totient n) one
