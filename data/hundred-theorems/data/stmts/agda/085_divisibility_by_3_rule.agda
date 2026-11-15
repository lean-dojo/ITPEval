-- Statement-only formalization of "Divisibility by 3 Rule" from Hundred Theorems item 085. This
-- file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _∣_
infix 2 _↔_
infixr 8 _^_

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

sumThrough : Nat → (Nat → Nat) → Nat
sumThrough zero term = term zero
sumThrough (suc n) term =
  sumThrough n term + term (suc n)

divisibility-by-3-rule : Set
divisibility-by-3-rule =
  (n : Nat) →
  (digits : Nat → Nat) →
  (3 ∣ sumThrough n (λ i → (10 ^ i) * digits i))
    ↔ (3 ∣ sumThrough n digits)
