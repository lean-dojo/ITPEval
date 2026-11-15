-- Statement-only formalization of miniF2F test problem imo_1982_p1: a near-additive
-- function on natural numbers constrained at 2, 3, and 9999. This file contains no proof.

module imo-1982-p1 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _<_)

infixr 3 _∨_

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

imo-1982-p1 : Set
imo-1982-p1 =
  (f : Nat → Nat) →
  ((m n : Nat) →
    (zero < m) ≡ true →
    (zero < n) ≡ true →
    (f (m + n) ≡ f m + f n) ∨
    (f (m + n) ≡ suc (f m + f n))) →
  f 2 ≡ zero →
  (zero < f 3) ≡ true →
  f 9999 ≡ 3333 →
  f 1982 ≡ 660
