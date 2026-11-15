-- Statement-only formalization of miniF2F test problem mathd_numbertheory_135. This file
-- contains no proof.

module mathd-numbertheory-135 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_ _≠_
infixr 8 _^_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

Not : Set → Set
Not P = P → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

Odd : Nat → Set
Odd n = Exists Nat (λ k → 2 * k + 1 ≡ n)

Digit : Nat → Set
Digit n = n ≤ 9

decimalValue : Nat → Nat → Nat → Nat
decimalValue A B C =
  100000000 * A +
  10000000 * B +
  1000000 * C +
  100000 * A +
  10000 * C +
  1000 * C +
  100 * B +
  10 * A +
  B

mathd-numbertheory-135 : Set
mathd-numbertheory-135 =
  (n A B C : Nat) →
  n ≡ 3 ^ 17 + 3 ^ 10 →
  11 ∣ (n + 1) →
  A ≠ B →
  B ≠ C →
  A ≠ C →
  Digit A →
  Digit B →
  Digit C →
  Odd A →
  Odd C →
  Not (3 ∣ B) →
  n ≡ decimalValue A B C →
  100 * A + 10 * B + C ≡ 129
