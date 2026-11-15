-- Statement-only formalization of miniF2F test problem imo_1997_p5: classification of
-- positive natural solutions to an exponential Diophantine equation. This file contains no proof.

module imo-1997-p5 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _<_)

infixr 4 _∧_
infixr 3 _∨_
infixr 8 _^_

record _∧_ (A B : Set) : Set where
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

Positive : Nat → Set
Positive n = (zero < n) ≡ true

imo-1997-p5 : Set
imo-1997-p5 =
  (x y : Nat) →
  (Positive x ∧ Positive y) →
  x ^ (y ^ 2) ≡ y ^ x →
  ((x , y) ≡ (1 , 1)) ∨
  ((x , y) ≡ (16 , 2)) ∨
  ((x , y) ≡ (27 , 3))
