-- Statement-only formalization of miniF2F test problem imo_1981_p6. This file contains no
-- proof.

module imo-1981-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infixr 2 _∧_
infixr 8 _^_

record _∧_ (A B : Set) : Set where
  field
    left  : A
    right : B

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

imo-1981-p6 : Set
imo-1981-p6 =
  (f : Nat → Nat → Nat) →
  (g : Nat → Nat) →
  ((y : Nat) → f 0 y ≡ y + 1) →
  ((x : Nat) → f (suc x) 0 ≡ f x 1) →
  ((x y : Nat) → f (suc x) (suc y) ≡ f x (f (suc x) y)) →
  g 0 ≡ 2 →
  ((n : Nat) → g (suc n) ≡ 2 ^ (g n)) →
  (((y : Nat) → f 4 (suc y) ≡ 2 ^ (f 4 y + 3) - 3) ∧
   (f 4 1981 ≡ g 1983 - 3))
