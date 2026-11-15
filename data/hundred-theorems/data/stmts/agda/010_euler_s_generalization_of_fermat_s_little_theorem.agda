-- Statement-only formalization of "Euler's Generalization of Fermat's Little Theorem" from
-- Hundred Theorems item 010. This file contains no proof.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat → Nat → Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc b) = false
natEqual (suc a) zero = false
natEqual (suc a) (suc b) = natEqual a b

coprimeBool : Nat → Nat → Bool
coprimeBool a b = natEqual (naturalGCD a b) 1

Coprime : Nat → Nat → Set
Coprime a b = naturalGCD a b ≡ 1

indicator : Bool → Nat
indicator false = zero
indicator true = 1

countCoprimeThrough : Nat → Nat → Nat
countCoprimeThrough n zero = zero
countCoprimeThrough n (suc bound) =
  countCoprimeThrough n bound +
  indicator (coprimeBool (suc bound) n)

totient : Nat → Nat
totient n = countCoprimeThrough n n

ModEq : Nat → Nat → Nat → Set
ModEq modulus left right =
  naturalMod left modulus ≡ naturalMod right modulus

euler-s-generalization-of-fermat-s-little-theorem : Set
euler-s-generalization-of-fermat-s-little-theorem =
  (a n : Nat) →
  Coprime a n →
  ModEq n (a ^ totient n) 1
