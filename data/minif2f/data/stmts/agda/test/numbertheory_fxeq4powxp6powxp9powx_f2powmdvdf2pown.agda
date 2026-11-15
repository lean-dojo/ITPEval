-- Statement-only formalization of miniF2F test problem
-- numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown. This file contains no proof.

module numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 2 _∧_
infix 4 _≤_ _<_ _∣_
infixr 8 _^_

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left : A
    right : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown : Set
numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown =
  (m n : Nat) →
  (f : Nat → Nat) →
  ((x : Nat) → f x ≡ 4 ^ x + 6 ^ x + 9 ^ x) →
  (zero < m ∧ zero < n) →
  m ≤ n →
  f (2 ^ m) ∣ f (2 ^ n)
