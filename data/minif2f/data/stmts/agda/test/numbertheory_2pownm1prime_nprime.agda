-- Statement-only formalization of miniF2F test problem numbertheory_2pownm1prime_nprime. This
-- file contains no proof.

module numbertheory_2pownm1prime_nprime where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _≤_ _<_ _∣_
infixr 3 _∨_
infixr 8 _^_

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

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

numbertheory_2pownm1prime_nprime : Set
numbertheory_2pownm1prime_nprime =
  (n : Nat) →
  zero < n →
  Prime (2 ^ n - 1) →
  Prime n
