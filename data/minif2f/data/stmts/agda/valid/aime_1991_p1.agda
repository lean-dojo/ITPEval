-- Statement-only formalization of miniF2F valid problem aime_1991_p1: positive natural
-- numbers satisfying two polynomial equations have sum of squares 146. This file contains
-- no proof.

module aime-1991-p1 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_; _<_)

infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

square : Nat → Nat
square n = n * n

aime-1991-p1 : Set
aime-1991-p1 =
  (x y : Nat) →
  NatLess zero x ∧ NatLess zero y →
  x * y + (x + y) ≡ 71 →
  square x * y + x * square y ≡ 880 →
  square x + square y ≡ 146
