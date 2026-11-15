-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_43. This file
-- contains no proof.

module mathd-numbertheory-43 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _∣_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

record IsGreatest
  (predicate : Nat → Set)
  (greatest : Nat) : Set where
  field
    member : predicate greatest
    upper-bound :
      (n : Nat) →
      predicate n →
      n ≤ greatest

mathd-numbertheory-43 : Set
mathd-numbertheory-43 =
  IsGreatest (λ n → 15 ^ n ∣ factorial 942) 233
