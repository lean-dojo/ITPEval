-- Statement-only formalization of miniF2F valid problem numbertheory_prmdvsneqnsqmodpeq0. This
-- file contains no proof.

module numbertheory_prmdvsneqnsqmodpeq0 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _≤_ _∣_
infixr 3 _∨_
infix 2 _↔_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record Prime (n : Nat) : Set where
  field
    at-least-two : suc (suc zero) ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ suc zero ∨ d ≡ n

magnitude : Int → Nat
magnitude (pos n) = n
magnitude (negsuc n) = suc n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

numbertheory_prmdvsneqnsqmodpeq0 : Set
numbertheory_prmdvsneqnsqmodpeq0 =
  (n : Int) →
  (p : Nat) →
  Prime p →
  ((p ∣ magnitude n) ↔
   (naturalMod (magnitude n * magnitude n) p ≡ zero))
